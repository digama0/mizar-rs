//! Structured diagnostic reporting and recovery primitives.
//!
//! See `notes/error-handling.md` for the overall design. This module provides
//! the reporting infrastructure; the migration of individual `panic!`/`assert!`
//! sites onto it happens in later phases.

use crate::error::DiagKind;
use crate::types::Span;
use annotate_snippets::{AnnotationKind, Group, Level, Origin, Renderer, Snippet};
use std::io::IsTerminal;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::Arc;

/// A zero-sized token witnessing that an error has already been reported.
///
/// It is constructible only through [`Reporter::error`], so a function returning
/// `Result<_, ErrorReported>` cannot signal failure without having emitted a
/// diagnostic first (cf. rustc's `ErrorGuaranteed`). Recovery code bubbles this
/// up with `?` to the nearest synchronization point.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct ErrorReported(());

/// The result type for decision-producing operations that may fail. On failure
/// the error has already been reported; the caller only needs to recover.
pub type MizResult<T> = Result<T, ErrorReported>;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Severity {
  Error,
  Warning,
  Note,
}

/// A structured diagnostic, shaped to lower onto `annotate-snippets`.
///
/// Phase 1 carries a single primary span + label; the representation is meant to
/// grow (secondary labels, notes, help) without changing call sites.
pub struct Diagnostic {
  pub severity: Severity,
  pub span: Span,
  /// The error itself, structured. Render it with [`std::fmt::Display`], or map it
  /// to a legacy Mizar error number with [`DiagKind::mizar`] for `.err` output.
  pub kind: DiagKind,
  pub label: Option<String>,
  /// Set when the diagnostic is about a *different* file than the article being
  /// verified — a dependency or a pre-accommodated artifact. `span` is then a byte
  /// offset into that file, and the reporter resolves `line:col` against it rather
  /// than against the article source.
  pub file: Option<PathBuf>,
}

impl Diagnostic {
  pub fn new(severity: Severity, span: Span, kind: impl Into<DiagKind>) -> Self {
    Self { severity, span, kind: kind.into(), label: None, file: None }
  }

  /// A diagnostic about another file, at a byte offset within it. Used by the
  /// dependency/artifact readers so their errors flow through the same sink (and
  /// are counted) rather than going out-of-band to stderr.
  pub fn in_file(
    severity: Severity, path: PathBuf, offset: Option<usize>, kind: impl Into<DiagKind>,
  ) -> Self {
    let span = offset.map_or(Span::NONE, |o| Span::at(o as u32));
    Self { severity, span, kind: kind.into(), label: None, file: Some(path) }
  }
  pub fn error(span: Span, kind: impl Into<DiagKind>) -> Self {
    Self::new(Severity::Error, span, kind)
  }
  pub fn warning(span: Span, kind: impl Into<DiagKind>) -> Self {
    Self::new(Severity::Warning, span, kind)
  }

  /// The rendered message.
  pub fn title(&self) -> String { self.kind.to_string() }
  /// Attach a label rendered on the underlined span (defaults to the title).
  pub fn label(mut self, label: impl Into<String>) -> Self {
    self.label = Some(label.into());
    self
  }
}

/// The sink through which all diagnostics flow. The default implementation
/// ([`WriteReporter`]) renders immediately and tallies errors/warnings, but this
/// is a trait object so alternate sinks (collecting, silent, LSP) can be swapped
/// in. Held as `Arc<dyn Reporter>` on `Global` and `ParserCore`.
pub trait Reporter: Send + Sync + std::fmt::Debug {
  fn emit(&self, diag: Diagnostic);
  fn errors(&self) -> u32;
  fn warnings(&self) -> u32;

  /// The 1-based `(line, col)` of a byte offset in the article source, if the
  /// source is available. Used both to display diagnostics and to drive the
  /// line-based options (`first_verbose_line`, `one_item`, the progress bar).
  fn line_col(&self, _offset: u32) -> Option<(u32, u32)> { None }

  /// The 1-based line of a byte offset, or `0` if the source is unavailable.
  fn line(&self, offset: u32) -> u32 { self.line_col(offset).map_or(0, |(l, _)| l) }

  /// Emit an error and return the [`ErrorReported`] token: `return Err(self.error(..))`.
  fn error(&self, diag: Diagnostic) -> ErrorReported {
    debug_assert!(matches!(diag.severity, Severity::Error));
    self.emit(diag);
    ErrorReported(())
  }
}

/// Byte offsets of the start of each line, for converting between byte offsets
/// and 1-based `line:col`. Shared by the reporter (offset → line:col, for
/// display and the line-based options) and the XML readers (line:col → offset,
/// when translating legacy positions against the loaded `.miz` source).
#[derive(Debug, Clone)]
pub struct LineMap {
  /// Byte offset of the start of each line.
  starts: Vec<u32>,
  /// Total source length in bytes.
  len: u32,
}

impl LineMap {
  pub fn new(source: &[u8]) -> Self {
    let mut starts = vec![0];
    starts.extend(memchr::memchr_iter(b'\n', source).map(|i| i as u32 + 1));
    LineMap { starts, len: source.len() as u32 }
  }

  /// The 1-based `(line, col)` of a byte offset.
  pub fn line_col(&self, offset: u32) -> (u32, u32) {
    let line = self.starts.partition_point(|&start| start <= offset).max(1);
    #[allow(clippy::indexing_slicing)]
    (line as u32, offset - self.starts[line - 1] + 1)
  }

  /// The byte offset of a 1-based `line:col`, clamped to the source length.
  pub fn offset(&self, line: u32, col: u32) -> u32 {
    if line == 0 {
      return self.len
    }
    let line_start = self.starts.get(line as usize - 1).copied().unwrap_or(self.len);
    (line_start + col.saturating_sub(1)).min(self.len)
  }

  /// Translate a legacy `line:col` start/end pair (with `end` line 0 meaning
  /// "no end") into a byte-offset [`Span`].
  pub fn span(&self, start: (u32, u32), end: (u32, u32)) -> Span {
    let s = self.offset(start.0, start.1);
    let e = if end.0 == 0 { s } else { self.offset(end.0, end.1) };
    Span::new(s, e)
  }
}

/// How many diagnostics [`WriteReporter`] will render before it stops and says so.
///
/// This is a display limit only: the error/warning counters keep incrementing, so
/// the export gate, the exit status, and anything else keying off
/// [`Reporter::errors`] see the true count. The Pascal implementation splits it the
/// same way — `errhan.Error` never caps (it only offers `-s`, halt on the *first*
/// error), while the `errflag` formatter that renders `.err` into the source caps at
/// `MaxErrNbr = 5000` and marks the truncation with error 499, "Too many errors".
/// The value matches Mizar's.
pub const MAX_DIAGNOSTICS: u32 = 5000;

/// The default reporter: renders each diagnostic to stderr immediately (with
/// source snippets when the source is available) and counts errors and warnings.
#[derive(Debug)]
pub struct WriteReporter {
  path: PathBuf,
  source: Option<String>,
  lines: Option<Arc<LineMap>>,
  errors: AtomicU32,
  warnings: AtomicU32,
  /// Diagnostics seen, capped-or-not, to drive [`MAX_DIAGNOSTICS`]. Distinct from
  /// `errors + warnings` because notes count toward the display limit too.
  seen: AtomicU32,
  /// A `LineMap` per dependency/artifact file that a diagnostic points into, built
  /// once and reused, so many diagnostics about one bad file don't each re-read it.
  dep_lines: std::sync::Mutex<std::collections::HashMap<PathBuf, Option<Arc<LineMap>>>>,
}

impl WriteReporter {
  pub fn new(path: PathBuf, source: Option<String>, lines: Option<Arc<LineMap>>) -> Self {
    Self {
      path,
      source,
      lines,
      errors: 0.into(),
      warnings: 0.into(),
      seen: 0.into(),
      dep_lines: Default::default(),
    }
  }

  /// The 1-based `line:col` of a byte offset in a dependency/artifact file, building
  /// and caching that file's [`LineMap`] once instead of re-reading it per diagnostic.
  fn dep_line_col(&self, file: &Path, offset: u32) -> Option<(u32, u32)> {
    let mut cache = self.dep_lines.lock().unwrap();
    cache
      .entry(file.to_owned())
      .or_insert_with(|| std::fs::read(file).ok().map(|b| Arc::new(LineMap::new(&b))))
      .as_ref()
      .map(|lm| lm.line_col(offset))
  }

  /// Resolve a [`Span`] to a byte range into the source, if one is available.
  fn byte_range(&self, span: Span) -> Option<(usize, usize)> {
    let source = self.source.as_deref()?;
    if span.is_none() {
      return None
    }
    let (a, b) = (span.start as usize, span.end.max(span.start) as usize);
    Some((a.min(source.len()), b.min(source.len())))
  }
}

impl Reporter for WriteReporter {
  fn errors(&self) -> u32 { self.errors.load(Ordering::Relaxed) }
  fn warnings(&self) -> u32 { self.warnings.load(Ordering::Relaxed) }

  fn line_col(&self, offset: u32) -> Option<(u32, u32)> {
    Some(self.lines.as_ref()?.line_col(offset))
  }

  fn emit(&self, diag: Diagnostic) {
    match diag.severity {
      Severity::Error => self.errors.fetch_add(1, Ordering::Relaxed),
      Severity::Warning => self.warnings.fetch_add(1, Ordering::Relaxed),
      Severity::Note => 0,
    };
    // Counters are bumped above this point, so suppression never hides an error
    // from the export gate or the exit status — it only stops the scrolling.
    let seen = self.seen.fetch_add(1, Ordering::Relaxed) + 1;
    if seen >= MAX_DIAGNOSTICS {
      if seen == MAX_DIAGNOSTICS {
        let title = format!("too many errors; suppressing further diagnostics after {seen}");
        let group = Group::with_title(Level::ERROR.primary_title(&title));
        eprintln!("{}", renderer().render(&[group]));
      }
      return
    }
    let level = match diag.severity {
      Severity::Error => Level::ERROR,
      Severity::Warning => Level::WARNING,
      Severity::Note => Level::NOTE,
    };
    let title = diag.title();
    // A diagnostic about another file (dependency / artifact): resolve `line:col`
    // against that file rather than the article source, and render an origin only.
    if let Some(file) = &diag.file {
      let path = file.to_string_lossy();
      let mut origin = Origin::path(path.as_ref());
      if !diag.span.is_none() {
        if let Some((line, col)) = self.dep_line_col(file, diag.span.start) {
          origin = origin.line(line as usize).char_column(col as usize);
        }
      }
      eprintln!("{}", renderer().render(&[level.primary_title(&title).element(origin)]));
      return
    }
    let path = self.path.to_string_lossy();
    let rendered = if let (Some(source), Some((a, b))) = (&self.source, self.byte_range(diag.span))
    {
      let mut ann = AnnotationKind::Primary.span(a..b);
      if let Some(label) = &diag.label {
        ann = ann.label(label.as_str());
      }
      let snippet = Snippet::source(source).line_start(1).path(path.as_ref()).annotation(ann);
      let group = level.primary_title(&title).element(snippet);
      renderer().render(&[group])
    } else {
      // No source snippet available: fall back to a title plus a file/line origin.
      let mut origin = Origin::path(path.as_ref());
      if let Some((line, col)) = self.line_col(diag.span.start).filter(|_| !diag.span.is_none()) {
        origin = origin.line(line as usize).char_column(col as usize);
      }
      renderer().render(&[level.primary_title(&title).element(origin)])
    };
    eprintln!("{rendered}");
  }
}

/// The code written to `.err` for a diagnostic with no legacy counterpart.
///
/// Deliberately outside the range `mizar.msg` defines (which tops out at 1999), so
/// an unmapped diagnostic is visibly ours rather than silently masquerading as a
/// Mizar error with a different meaning.
pub const UNMAPPED_CODE: u32 = 9999;

/// Writes a Mizar-compatible `.err` file instead of rendering for humans.
///
/// The format is `errhan.WriteError`'s: one `line col code` triple per diagnostic,
/// all 1-based. Entries are buffered and sorted by `(line, col)` on [`Self::finish`]
/// rather than streamed, because our diagnostics are *not* emitted in source order:
/// an error about a construct is positioned at its head keyword, which precedes any
/// error recovered from inside it, and parsing interleaves with analysis item by
/// item. The Pascal system has the same property — `errhan` appends in emission
/// order and `errflag` insertion-sorts by `(Line, Col)` when it renders.
#[derive(Debug)]
pub struct ErrFileReporter {
  path: PathBuf,
  lines: Option<Arc<LineMap>>,
  errors: AtomicU32,
  warnings: AtomicU32,
  entries: std::sync::Mutex<Vec<(u32, u32, u32)>>,
}

impl ErrFileReporter {
  /// `path` is the `.err` file to write; `lines` maps byte offsets of the article
  /// source to `line:col`.
  pub fn new(path: PathBuf, lines: Option<Arc<LineMap>>) -> Self {
    Self { path, lines, errors: 0.into(), warnings: 0.into(), entries: Default::default() }
  }

  /// Sort by position and write the file. Mirrors `errflag`'s sort; without it the
  /// triples come out in emission order, which is not source order.
  pub fn finish(&self) -> std::io::Result<()> {
    use std::io::Write;
    #[allow(clippy::unwrap_used)]
    let mut entries = self.entries.lock().unwrap().clone();
    entries.sort_unstable();
    let mut out = std::io::BufWriter::new(std::fs::File::create(&self.path)?);
    for (line, col, code) in entries {
      writeln!(out, "{line} {col} {code}")?;
    }
    out.flush()
  }
}

/// Write the file however the run ends. `with_reader` has several early-return
/// paths (a missing `.miz`, a failed artifact load), and on each of those the `.err`
/// is exactly what the caller wants — those are the runs that produced errors.
impl Drop for ErrFileReporter {
  fn drop(&mut self) {
    if let Err(e) = self.finish() {
      eprintln!("error: could not write {}: {e}", self.path.to_string_lossy());
    }
  }
}

impl Reporter for ErrFileReporter {
  fn errors(&self) -> u32 { self.errors.load(Ordering::Relaxed) }
  fn warnings(&self) -> u32 { self.warnings.load(Ordering::Relaxed) }

  fn line_col(&self, offset: u32) -> Option<(u32, u32)> {
    Some(self.lines.as_ref()?.line_col(offset))
  }

  fn emit(&self, diag: Diagnostic) {
    match diag.severity {
      Severity::Error => self.errors.fetch_add(1, Ordering::Relaxed),
      Severity::Warning => self.warnings.fetch_add(1, Ordering::Relaxed),
      Severity::Note => 0,
    };
    // A diagnostic about another file has no position in *this* article; Mizar has
    // no way to express that in `.err`, so record it at the head of the file.
    let (line, col) = match self.line_col(diag.span.start).filter(|_| !diag.span.is_none()) {
      Some(pos) if diag.file.is_none() => pos,
      _ => (1, 1),
    };
    #[allow(clippy::unwrap_used)]
    self.entries.lock().unwrap().push((line, col, diag.kind.mizar().unwrap_or(UNMAPPED_CODE)));
  }
}

fn renderer() -> Renderer {
  if std::io::stderr().is_terminal() {
    Renderer::styled()
  } else {
    Renderer::plain()
  }
}
