use crate::format::FormatterConfig;
use crate::types::*;
use clap::{ArgAction, CommandFactory, Parser, ValueEnum};
use enum_map::EnumMap;
use indicatif::{MultiProgress, ProgressBar, ProgressDrawTarget, ProgressStyle};
use itertools::Itertools;
use std::cmp::Ordering;
use std::collections::{BTreeMap, HashMap};
use std::fmt::Display;
use std::io::Write;
use std::sync::atomic::AtomicBool;
use std::sync::Mutex;

mod accom;
mod analyze;
mod ast;
mod bignum;
mod cache;
mod checker;
mod equate;
mod export;
mod format;
mod global;
mod parser;
mod reader;
mod types;
mod unify;
mod util;
mod write;

pub use global::*;

pub fn stat(s: &'static str) {
  *STATS.lock().unwrap().get_or_insert_with(HashMap::new).entry(s).or_default() += 1;
}

#[macro_export]
macro_rules! vprintln {
  ($($args:tt)*) => {
    if $crate::verbose() {
      eprintln!($($args)*)
    }
  };
}

#[allow(unused)]
#[macro_export]
macro_rules! vdbg {
  ($($args:tt)*) => {
    if $crate::verbose() {
      dbg!($($args)*)
    } else {
      ($($args)*)
    }
  };
}

static VERBOSE: AtomicBool = AtomicBool::new(false);
pub fn verbose() -> bool { DEBUG && VERBOSE.load(std::sync::atomic::Ordering::SeqCst) }
pub fn set_verbose(b: bool) { VERBOSE.store(b, std::sync::atomic::Ordering::SeqCst) }

static STATS: Mutex<Option<HashMap<&'static str, u32>>> = Mutex::new(None);

fn print_stats_and_exit() {
  let mut g = STATS.lock().unwrap();
  let mut vec: Vec<_> = g.get_or_insert_with(HashMap::new).iter().collect();
  vec.sort();
  for (s, i) in vec {
    println!("{s}: {i}");
  }
  std::process::exit(0)
}

#[derive(Clone)]
struct Progress {
  multi: MultiProgress,
  main: Option<ProgressBar>,
  style: ProgressStyle,
}

impl Progress {
  fn new(num_jobs: usize, known_len: bool) -> Option<Self> {
    let multi = MultiProgress::with_draw_target(ProgressDrawTarget::stdout_with_hz(5));
    if multi.is_hidden() {
      return None
    }
    multi.set_alignment(indicatif::MultiProgressAlignment::Bottom);
    Some(Progress {
      main: if num_jobs > 1 { Some(multi.add(ProgressBar::new(num_jobs as u64))) } else { None },
      style: if known_len {
        ProgressStyle::with_template("{msg:14} [{pos:>5}] {wide_bar} {elapsed_precise}").unwrap()
      } else {
        ProgressStyle::with_template("{msg:14} [{pos:>5}] {spinner} {elapsed_precise}").unwrap()
      },
      multi,
    })
  }
}

const fn bool_to_str(b: bool) -> &'static str {
  if b {
    "true"
  } else {
    "false"
  }
}

#[derive(Debug, clap::Args)]
struct CliPasses;
#[derive(Debug, clap::Args)]
struct CliOther;
#[derive(Debug, clap::Args)]
struct CliDebug;
#[derive(Debug, clap::Args)]
struct CliUnsound;

/// Mizar verifier toolchain. Common usage cases:
///
///   * mizar-rs -dex --overwrite-prel
///     Read the MML .miz files and generate the prel/ folder
///   * mizar-rs
///     Parse and compile the whole MML from scratch
///   * mizar-rs nat_4 --one-file
///     Parse and compile only article nat_4
///   * mizar-rs nat_4 14 --unify-insts
///     Give debugging info regarding the item at line 14 of article nat_4
#[derive(Debug, clap::Parser)]
#[command(author, version, about, long_about, verbatim_doc_comment)]
struct Cli {
  /// The name of the first file to process, or the index of the file in `mml.lar`
  file: Option<String>,
  /// The line on which to turn on verbose mode
  first_verbose_line: Option<u32>,

  #[command(flatten, next_help_heading = "Pass selection options")]
  _passes: CliPasses,
  /// Enables (only) the checker, checking 'by' proofs straight from .xml
  #[arg(short = 'c', long)]
  checker: bool,
  /// Disables the checker, checking the proof skeleton but not individual by steps
  #[arg(short = 'C', long)]
  no_checker: bool,
  /// Enables (only) the analyzer, checking the proof skeleton but not individual by steps
  #[arg(short = 'a', long)]
  analyzer: bool,
  /// Disables the analyzer
  #[arg(short = 'A', long)]
  no_analyzer: bool,
  /// Enables (only) the exporter, doing the minimal amount of work to produce theorem statements
  #[arg(short = 'e', long)]
  export: bool,
  /// Disables the exporter
  #[arg(short = 'E', long)]
  no_export: bool,
  /// Check that the exported statements exactly match the `miz/mizshare/prel/` directory
  #[arg(short = 'v', long)]
  verify_export: bool,
  /// Produce exported statements to the `miz/prel/` directory (requires `-e`)
  #[arg(short = 'x', long)]
  xml_export: bool,
  /// Disables the accomodator. (requires `-P`)
  #[arg(short = 'M', long)]
  no_accom: bool,
  /// Disables the parser, reading .wsx files instead of .miz
  #[arg(short = 'P', long)]
  no_parser: bool,
  /// Disables name resolution, reading .msx instead of .wsx (requires `-P`)
  #[arg(short = 'N', long)]
  no_nameck: bool,

  /// Strictly follow dependency order, instead of using `prel/`
  #[arg(short = 'd', long)]
  dep_order: bool,

  /// The number of threads to use (currently only file level parallelism is supported)
  #[arg(short = 'j', long, default_value_t = if DEBUG { 1 } else { num_cpus::get() })]
  parallelism: usize,

  /// Use `mizar-rs` as a frontend for the original mizar `verifier`
  #[arg(long)]
  orig_mizar: bool,

  /// Exit after processing the first verbose item
  #[arg(long, num_args = 0..=1, action = ArgAction::Set, default_value = "true",
    require_equals = true, default_missing_value = "true", hide_possible_values = true)]
  one_item: bool,

  /// Exit after processing the first selected file
  #[arg(long, num_args = 0..=1, action = ArgAction::Set, default_value = bool_to_str(DEBUG),
    require_equals = true, default_missing_value = "true", hide_possible_values = true)]
  one_file: bool,

  /// Index of the last file to process, if specified
  #[arg(long)]
  last_file: Option<usize>,

  /// Disable the checker while not in verbose mode
  #[arg(long, num_args = 0..=1, action = ArgAction::Set, default_value = bool_to_str(DEBUG),
    require_equals = true, default_missing_value = "true", hide_possible_values = true)]
  skip_to_verbose: bool,

  #[command(flatten, next_help_heading = "Other options")]
  _other: CliOther,
  /// Panic on the first error
  #[arg(long, num_args = 0..=1, action = ArgAction::Set, default_value = bool_to_str(DEBUG),
    require_equals = true, default_missing_value = "true", hide_possible_values = true)]
  panic_on_fail: bool,

  /// Write exported statements to `miz/mizshare/prel/` instead of `miz/prel/`,
  /// overwriting the originals
  #[arg(long, num_args = 0..=1, action = ArgAction::Set, default_value = bool_to_str(false),
    require_equals = true, default_missing_value = "true", hide_possible_values = true)]
  overwrite_prel: bool,
  /// Always read cross-article theorems from `prel/` instead of from memory
  #[arg(long)]
  no_cache: bool,
  /// Only show the main progress bar
  #[arg(long)]
  no_multi_progress: bool,
  /// Don't show the fancy progress bar
  #[arg(long)]
  no_progress: bool,

  #[command(flatten, next_help_heading = "Debugging tools")]
  _debug: CliDebug,
  /// Print a header at every top level item
  #[arg(long, num_args = 0..=1, action = ArgAction::Set, default_value = bool_to_str(false),
    require_equals = true, default_missing_value = "true", hide_possible_values = true)]
  top_item_header: bool,
  /// Print the full AST for each item, even when not in verbose mode
  #[arg(long, num_args = 0..=1, action = ArgAction::Set, default_value = bool_to_str(false),
    require_equals = true, default_missing_value = "true", hide_possible_values = true)]
  always_verbose_item: bool,
  /// Print a header at each item
  #[arg(long, num_args = 0..=1, action = ArgAction::Set, default_value = bool_to_str(DEBUG),
    require_equals = true, default_missing_value = "true", hide_possible_values = true)]
  item_header: bool,
  /// Print the checker input facts in verbose mode
  #[arg(long, num_args = 0..=1, action = ArgAction::Set, default_value = bool_to_str(DEBUG),
    require_equals = true, default_missing_value = "true", hide_possible_values = true)]
  checker_inputs: bool,
  /// Print the checker header in verbose mode
  #[arg(long, num_args = 0..=1, action = ArgAction::Set, default_value = bool_to_str(DEBUG),
    require_equals = true, default_missing_value = "true", hide_possible_values = true)]
  checker_header: bool,
  /// Print the processed checker conjuncts in verbose mode
  #[arg(long, num_args = 0..=1, action = ArgAction::Set, default_value = bool_to_str(DEBUG),
    require_equals = true, default_missing_value = "true", hide_possible_values = true)]
  checker_conjuncts: bool,
  /// Print the checker result in verbose mode
  #[arg(long, num_args = 0..=1, action = ArgAction::Set, default_value = bool_to_str(DEBUG),
    require_equals = true, default_missing_value = "true", hide_possible_values = true)]
  checker_result: bool,
  /// Print the input to the unifier module in verbose mode
  #[arg(long, num_args = 0..=1, action = ArgAction::Set, default_value = bool_to_str(DEBUG),
    require_equals = true, default_missing_value = "true", hide_possible_values = true)]
  unify_header: bool,
  /// Print the instantiation produced by the unifier in verbose mode
  #[arg(long, num_args = 0..=1, action = ArgAction::Set, default_value = bool_to_str(DEBUG),
    require_equals = true, default_missing_value = "true", hide_possible_values = true)]
  unify_insts: bool,

  /// Dump the contents of various system components,
  /// or `--dump` without arguments to print everything
  #[arg(long, value_delimiter = ',', num_args = 0..)]
  dump: Option<Vec<DumpKind>>,

  #[command(flatten, next_help_heading = "Bugs and unsound flags")]
  _unsound: CliUnsound,
  /// This is an UNSOUND FLAG that enables checking of `P[a] & ... & P[b]`
  /// equality by checking only the endpoints `P[a]` and `P[b]`.
  /// This is needed to check some MML proofs
  #[arg(long, num_args = 0..=1, action = ArgAction::Set, default_value = bool_to_str(true),
    require_equals = true, default_missing_value = "true", hide_possible_values = true)]
  legacy_flex_handling: bool,

  /// This is completely wrong and UNSOUND behavior, when expanding a flex-and
  /// only the first conjunct is used, but aofa_l00 can't be checked without
  /// it (the proof should be patched).
  #[arg(long, num_args = 0..=1, action = ArgAction::Set, default_value = bool_to_str(true),
    require_equals = true, default_missing_value = "true", hide_possible_values = true)]
  flex_expansion_bug: bool,

  /// This is buggy behavior, but not unsound. It is required to interpret some MML files.
  #[arg(long, num_args = 0..=1, action = ArgAction::Set, default_value = bool_to_str(true),
    require_equals = true, default_missing_value = "true", hide_possible_values = true)]
  attr_sort_bug: bool,
}

macro_rules! mk_dump {
  (struct $dump:ident {
    $($id:ident,)*
  }) => {
    #[derive(Clone, Debug, Default)]
    pub struct $dump {
      $(pub $id: bool,)*
    }
    #[derive(Clone, Copy, Debug, ValueEnum)]
    #[allow(non_camel_case_types)]
    enum DumpKind { $($id,)* }
    impl From<&Option<Vec<DumpKind>>> for $dump {
      fn from(it: &Option<Vec<DumpKind>>) -> $dump {
        match it {
          None => Dump { $($id: false),* },
          Some(it) if it.is_empty() => Dump { $($id: true),* },
          Some(it) => {
            let mut out = $dump::default();
            for &k in it {
              match k { $(DumpKind::$id => out.$id = true,)* }
            }
            out
          }
        }
      }
    }
  }
}
mk_dump! {
  struct Dump {
    config,
    constructors,
    requirements,
    notations,
    clusters,
    definitions,
    libraries,
    formatter,
  }
}

// clap::builder::via_prelude::_ValueParserViaParse
#[derive(Clone, Debug)]
pub struct Config {
  pub top_item_header: bool,
  pub always_verbose_item: bool,
  pub item_header: bool,
  pub checker_inputs: bool,
  pub checker_header: bool,
  pub checker_conjuncts: bool,
  pub checker_result: bool,
  pub unify_header: bool,
  pub unify_insts: bool,

  pub dump: Dump,

  pub accom_enabled: bool,
  pub parser_enabled: bool,
  pub nameck_enabled: bool,
  pub analyzer_enabled: bool,
  pub analyzer_full: bool,
  pub checker_enabled: bool,
  pub exporter_enabled: bool,
  pub verify_export: bool,
  pub xml_export: bool,
  pub overwrite_prel: bool,
  pub cache_prel: bool,

  // Unsound flags //
  /// This flag enables checking of `P[a] & ... & P[b]` equality by checking
  /// only the endpoints `P[a]` and `P[b]`. This is unsound, but needed to
  /// check some proofs
  pub legacy_flex_handling: bool,
  /// This is completely wrong and unsound behavior, when expanding a flex-and
  /// only the first conjunct is used, but aofa_l00 can't be checked without
  /// it (the proof should be patched).
  pub flex_expansion_bug: bool,

  /// Cluster lists in `Attrs` are supposed to be sorted, but Mizar fails
  /// to re-sort after some operations that can change relative sort order,
  /// notably instantiation. Unfortunately this is user-visible because of
  /// implicit argument inference in ambiguous cases; afinsq_2 needs a bunch
  /// of `qua`s and I think there are some cases which are just impossible
  /// to specify this way. (This is not unsound.)
  pub attr_sort_bug: bool,

  pub panic_on_fail: bool,
  pub first_verbose_line: Option<u32>,
  pub one_item: bool,
  pub skip_to_verbose: bool,
}

const DEBUG: bool = cfg!(debug_assertions);
const GC_THRESHOLD: usize = 5000;
const READ_MAX_LINE_COUNT: bool = true;

impl FormatterConfig {
  const DEFAULT: Self = Self {
    enable_formatter: true,
    show_infer: false,
    show_only_infer: false,
    show_priv: false,
    show_marks: true,
    show_invisible: false,
    show_orig: true,
    upper_clusters: false,
    both_clusters: false,
    negation_sugar: true,
  };
}

fn conflict(msg: impl Display) -> ! {
  Cli::command().error(clap::error::ErrorKind::ArgumentConflict, msg).exit()
}

fn main() {
  let cli = Cli::parse();
  let enable = cli.analyzer || cli.checker || cli.export;
  let disable = cli.no_analyzer || cli.no_checker || cli.no_export;
  if enable && disable {
    conflict("can't use positive and negative pass selectors together")
  }
  let mut cfg = Config {
    accom_enabled: !cli.no_accom,
    parser_enabled: !cli.no_parser,
    nameck_enabled: !cli.no_nameck,
    analyzer_enabled: if enable { cli.analyzer } else { !cli.no_analyzer },
    analyzer_full: Default::default(),
    checker_enabled: if enable { cli.checker } else { !cli.no_checker },
    exporter_enabled: if enable { cli.export } else { !cli.no_export },
    verify_export: cli.verify_export,
    xml_export: cli.xml_export,
    overwrite_prel: cli.overwrite_prel,
    cache_prel: Default::default(),

    top_item_header: cli.top_item_header,
    always_verbose_item: cli.always_verbose_item,
    item_header: cli.item_header,
    checker_inputs: cli.checker_inputs,
    checker_header: cli.checker_header,
    checker_conjuncts: cli.checker_conjuncts,
    checker_result: cli.checker_result,
    unify_header: cli.unify_header,
    unify_insts: cli.unify_insts,

    dump: (&cli.dump).into(),

    legacy_flex_handling: cli.legacy_flex_handling,
    flex_expansion_bug: cli.flex_expansion_bug,
    attr_sort_bug: cli.attr_sort_bug,

    panic_on_fail: cli.panic_on_fail,
    first_verbose_line: cli.first_verbose_line, // None,
    one_item: cli.one_item,
    skip_to_verbose: cli.skip_to_verbose,
  };

  const FIRST_FILE: usize = 0;
  const LAST_FILE: Option<usize> = None; //Some(11);

  // set_verbose(true);
  // let path = MizPath(Article::from_bytes(b"TEST"), "../test/text/test".into());
  // path.with_reader(&cfg, |v| v.run_checker(&path));
  // print_stats_and_exit(cfg.parallelism);
  cfg.analyzer_full = cfg.analyzer_enabled;
  cfg.accom_enabled |= cfg.parser_enabled; // parser needs accom
  cfg.nameck_enabled |= cfg.parser_enabled; // parser needs nameck
  cfg.analyzer_full |= cfg.checker_enabled; // checker needs analyzer_full (if analyzer is used)
  cfg.cache_prel = !cfg.one_item && !cli.no_cache;
  cfg.exporter_enabled &= cfg.xml_export || cfg.verify_export || cfg.cache_prel;
  cfg.analyzer_enabled |= cfg.exporter_enabled; // exporter needs (quick) analyzer
  if cfg.cache_prel && cli.dep_order && cfg.verify_export {
    conflict("VERIFY_EXPORT and DEP_ORDER + CACHE are incompatible")
  }
  let one_file = cli.one_file;

  let file = std::fs::read_to_string("miz/mizshare/mml.lar").unwrap();
  let mml_vct =
    &if cfg.accom_enabled { std::fs::read("miz/mizshare/mml.vct").unwrap() } else { vec![] };
  let mut jobs = file.lines().enumerate().collect_vec();
  let first_file = match cli.file {
    None => FIRST_FILE,
    Some(n) => n.parse().unwrap_or_else(|_| {
      let n = n.to_lowercase();
      jobs.iter().position(|s| s.1 == n).unwrap_or_else(|| {
        Cli::command().error(clap::error::ErrorKind::InvalidValue, "article not found").exit()
      })
    }),
  };
  if cfg.dump.config {
    println!("config: {cfg:#?}");
    match jobs.get(first_file) {
      Some(&(_, s)) => println!("first_file: {first_file} = {s}"),
      None => println!("first_file: {first_file}"),
    }
    println!("one_file: {one_file}");
  }
  if cfg.cache_prel {
    cache::init_cache(jobs.iter().map(|&(i, x)| (x, cli.dep_order && i >= first_file)))
  }
  if let Some(n) = cli.last_file.or(LAST_FILE) {
    jobs.truncate(n + 1)
  }
  drop(jobs.drain(..first_file));
  if one_file {
    jobs.truncate(1)
  }
  if jobs.is_empty() {
    println!("nothing to do");
    std::process::exit(0)
  }
  let parallelism = cli.parallelism.min(jobs.len());
  let progress = &if !cli.no_progress {
    Progress::new(jobs.len(), cfg.parser_enabled && READ_MAX_LINE_COUNT)
  } else {
    None
  };

  ctrlc::set_handler(print_stats_and_exit).expect("Error setting Ctrl-C handler");

  let jobs = &Mutex::new(jobs.into_iter());
  let running = &*std::iter::repeat_with(|| {
    (progress.as_ref().filter(|_| !cli.no_multi_progress))
      .map(|p| p.multi.insert(0, ProgressBar::hidden()).with_style(p.style.clone()))
  })
  .take(parallelism)
  .collect_vec();
  if let Some(p) = progress {
    if let Some(m) = &p.main {
      m.tick()
    }
    p.multi.set_move_cursor(true);
  }
  let cfg = &cfg;
  std::thread::scope(|s| {
    for thread in running {
      s.spawn(move || {
        while let Some((i, s)) = {
          let mut lock = jobs.lock().unwrap();
          lock.next()
        } {
          let path = MizPath::new(s);
          if let Some(thread) = &thread {
            thread.set_message(format!("{i:4}: {s}"));
            thread.set_length(1);
            thread.set_position(0);
            thread.reset_elapsed();
          }
          let start = std::time::Instant::now();
          if let Err(_payload) = std::panic::catch_unwind(|| {
            if cli.orig_mizar {
              if cfg.accom_enabled {
                let mut cmd = std::process::Command::new("miz/mizbin/accom");
                cmd.arg("-lqs");
                let output = cmd.arg(format!("{}.miz", path.mml().display())).output().unwrap();
                if !output.status.success() {
                  eprintln!("\nfile {} failed. Output:", path.art);
                  std::io::stderr().write_all(&output.stderr).unwrap();
                  std::io::stdout().write_all(&output.stdout).unwrap();
                  std::io::stdout().flush().unwrap();
                  panic!("mizar accom failed")
                }
              }
              let mut cmd = std::process::Command::new("miz/mizbin/verifier");
              let cmd = match (cfg.analyzer_enabled, cfg.checker_enabled) {
                (true, false) => cmd.arg("-a"),
                (false, true) => cmd.arg("-c"),
                (true, true) => &mut cmd,
                (false, false) => panic!("unsupported"),
              };
              let output = cmd.arg(format!("{}.miz", path.mml().display())).output().unwrap();
              if !output.status.success() {
                eprintln!("\nfile {} failed. Output:", path.art);
                std::io::stderr().write_all(&output.stderr).unwrap();
                std::io::stdout().write_all(&output.stdout).unwrap();
                std::io::stdout().flush().unwrap();
                panic!("mizar verifier failed")
              }
              // println!("{}", String::from_utf8(output.stdout).unwrap());
            } else if cfg.parser_enabled || cfg.analyzer_enabled {
              path.with_reader(cfg, thread.as_ref(), mml_vct, &mut |v, p| v.run_analyzer(&path, p));
            } else if cfg.checker_enabled {
              path.with_reader(cfg, thread.as_ref(), mml_vct, &mut |v, _| v.run_checker(&path));
            }
          }) {
            println!("error: {i}: {s} panicked");
            stat("panic");
            if cfg.panic_on_fail {
              std::process::abort()
            }
          }
          if let Some(p) = progress.as_ref().filter(|p| !p.multi.is_hidden()) {
            let msg = format!("{i:4}: {s:8} in {:.3}s", start.elapsed().as_secs_f32());
            p.multi.println(msg).unwrap();
          } else {
            println!("{i:4}: {s:8} in {:.3}s", start.elapsed().as_secs_f32())
          }
          if let Some(thread) = &thread {
            if let Some(len) = thread.length() {
              thread.set_position(len);
            }
          }
          if let Some(main) = progress.as_ref().and_then(|p| p.main.as_ref()) {
            main.inc(1)
          }
          if one_file || LAST_FILE == Some(i) {
            break
          }
        }
        if let Some(p) = progress {
          p.multi.set_move_cursor(false);
        }
        if let Some(thread) = thread {
          thread.finish_and_clear();
        }
      });
    }
  });
  if let Some(p) = progress {
    drop(p.multi.clear());
  }
  // std::thread::sleep(std::time::Duration::from_secs(60 * 60));
  print_stats_and_exit();
}
