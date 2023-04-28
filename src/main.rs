use crate::format::FormatterConfig;
use crate::types::*;
use enum_map::EnumMap;
use indicatif::{MultiProgress, ProgressBar, ProgressDrawTarget, ProgressStyle};
use itertools::Itertools;
use std::cmp::Ordering;
use std::collections::{BTreeMap, HashMap};
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

  pub dump_constructors: bool,
  pub dump_requirements: bool,
  pub dump_notations: bool,
  pub dump_clusters: bool,
  pub dump_definitions: bool,
  pub dump_libraries: bool,
  pub dump_formatter: bool,

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
  pub first_verbose_item: Option<u32>,
  pub one_item: bool,
  pub first_verbose_checker: Option<u32>,
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

fn main() {
  let mut cfg = Config {
    top_item_header: false,
    always_verbose_item: false,
    item_header: DEBUG,
    checker_inputs: DEBUG,
    checker_header: DEBUG,
    checker_conjuncts: DEBUG,
    checker_result: DEBUG,
    unify_header: DEBUG,
    unify_insts: DEBUG,

    dump_constructors: false,
    dump_requirements: false,
    dump_notations: false,
    dump_clusters: false,
    dump_definitions: false,
    dump_libraries: false,
    dump_formatter: false,

    accom_enabled: true,
    parser_enabled: true,
    nameck_enabled: true,
    analyzer_enabled: true,
    analyzer_full: true,
    checker_enabled: true,
    exporter_enabled: true,
    verify_export: false,
    xml_export: false,
    overwrite_prel: false,
    cache_prel: true,

    legacy_flex_handling: true,
    flex_expansion_bug: true,
    attr_sort_bug: true,

    panic_on_fail: DEBUG,
    first_verbose_item: None,
    one_item: false,
    first_verbose_checker: None,
    skip_to_verbose: DEBUG,
  };

  const FIRST_FILE: usize = 0;
  const LAST_FILE: Option<usize> = None; //Some(11);

  // set_verbose(true);
  // let path = MizPath(Article::from_bytes(b"TEST"), "../test/text/test".into());
  // path.with_reader(&cfg, |v| v.run_checker(&path));
  // print_stats_and_exit(cfg.parallelism);
  cfg.parser_enabled = std::env::var("NO_PARSER").is_err();
  cfg.nameck_enabled = std::env::var("NO_NAME_CHECK").is_err();
  cfg.analyzer_enabled = std::env::var("NO_ANALYZER").is_err();
  cfg.analyzer_full = cfg.analyzer_enabled;
  cfg.checker_enabled = std::env::var("NO_CHECKER").is_err();
  cfg.accom_enabled = std::env::var("NO_ACCOM").is_err();
  cfg.verify_export = std::env::var("VERIFY_EXPORT").is_ok();
  cfg.xml_export = std::env::var("XML_EXPORT").is_ok();
  cfg.exporter_enabled = std::env::var("NO_EXPORT").is_err();
  cfg.accom_enabled |= cfg.parser_enabled; // parser needs accom
  cfg.nameck_enabled |= cfg.parser_enabled; // parser needs nameck
  cfg.analyzer_full |= cfg.checker_enabled; // checker needs analyzer_full (if analyzer is used)
  cfg.one_item = std::env::var("ONE_ITEM").is_ok();
  cfg.cache_prel = !cfg.one_item && std::env::var("NO_CACHE").is_err();
  cfg.exporter_enabled &= cfg.xml_export || cfg.verify_export || cfg.cache_prel;
  cfg.analyzer_enabled |= cfg.exporter_enabled; // exporter needs (quick) analyzer
  let orig_mizar = std::env::var("ORIG_MIZAR").is_ok();
  let dep_order = std::env::var("DEP_ORDER").is_ok();
  assert!(
    !cfg.cache_prel || !dep_order || !cfg.verify_export,
    "VERIFY_EXPORT and DEP_ORDER + CACHE are incompatible"
  );
  let one_file = DEBUG || std::env::var("ONE_FILE").is_ok();
  let parallelism = if DEBUG || one_file { 1 } else { 8 };
  cfg.panic_on_fail |= std::env::var("PANIC_ON_FAIL").is_ok();
  let progress = std::env::var("NO_PROGRESS").is_err();

  let mut args = std::env::args().skip(1);
  let first_file = args.next().and_then(|s| s.parse().ok()).unwrap_or(FIRST_FILE);
  if let Some(n) = args.next().and_then(|s| s.parse().ok()) {
    cfg.first_verbose_item = Some(n)
  }

  let file = std::fs::read_to_string("miz/mizshare/mml.lar").unwrap();
  let mml_vct =
    &if cfg.accom_enabled { std::fs::read("miz/mizshare/mml.vct").unwrap() } else { vec![] };
  let mut jobs = file.lines().enumerate().collect_vec();
  if cfg.cache_prel {
    cache::init_cache(jobs.iter().map(|&(i, x)| (x, dep_order && i >= first_file)))
  }
  if let Some(n) = LAST_FILE {
    jobs.truncate(n + 1)
  }
  drop(jobs.drain(..first_file));
  if one_file {
    jobs.truncate(1)
  }
  let progress = if progress {
    Progress::new(jobs.len(), cfg.parser_enabled && READ_MAX_LINE_COUNT)
  } else {
    None
  };

  ctrlc::set_handler(print_stats_and_exit).expect("Error setting Ctrl-C handler");

  let jobs = &Mutex::new(jobs.into_iter());
  let running = &*std::iter::repeat_with(|| {
    (progress.as_ref())
      .map(|p| p.multi.insert(0, ProgressBar::hidden()).with_style(p.style.clone()))
  })
  .take(parallelism)
  .collect_vec();
  if let Some(p) = &progress {
    if let Some(m) = &p.main {
      m.tick()
    }
    p.multi.set_move_cursor(true);
  }
  let cfg = &cfg;
  std::thread::scope(|s| {
    for thread in running {
      let progress = progress.clone();
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
            if orig_mizar {
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
        if let Some(p) = &progress {
          p.multi.set_move_cursor(false);
        }
        if let Some(thread) = thread {
          thread.finish_and_clear();
        }
      });
    }
  });
  if let Some(p) = &progress {
    drop(p.multi.clear());
  }
  // std::thread::sleep(std::time::Duration::from_secs(60 * 60));
  print_stats_and_exit();
}
