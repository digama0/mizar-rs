use crate::types::{Article, Formula, Position};
use crate::{Global, LocalContext, MizPath};

#[derive(PartialEq, Eq)]
enum Severity {
  Error,
  #[allow(unused)]
  Warning,
}

#[derive(Debug)]
pub enum AccomError {
  TheoremsNotFound(Article),
  SchemesNotFound(Article),
}

impl AccomError {
  pub fn report(self, art: Article, pos: Position) -> bool {
    let severity = Severity::Error;
    let msg = match self {
      AccomError::TheoremsNotFound(art) => format!(
        "theorems for {art} not found (looked in {})",
        MizPath { art }.to_path(false, false, "the").to_string_lossy()
      ),
      AccomError::SchemesNotFound(art) => format!(
        "schemes for {art} not found (looked in {})",
        MizPath { art }.to_path(false, false, "sch").to_string_lossy()
      ),
    };
    let file = MizPath { art }.to_path(true, false, "miz");
    let sev = match severity {
      Severity::Error => "error",
      Severity::Warning => "warning",
    };
    eprintln!("{}:{pos:?}: {sev}: {msg}", file.to_string_lossy());
    severity == Severity::Error
  }
}

#[derive(Debug)]
pub enum MizError {
  UnexpectedPragma(String),
  IterEqualityNotAnEquality(Box<Formula>),
}

impl MizError {
  pub fn report(self, art: Article, pos: Position, _g: &Global, lc: &LocalContext) -> bool {
    let severity = Severity::Error;
    let msg = match &self {
      MizError::UnexpectedPragma(pragma) => format!("unknown pragma '{pragma}'"),
      MizError::IterEqualityNotAnEquality(f) => format!("not an equality: {}", lc.pp(f)),
    };
    let file = MizPath { art }.to_path(true, false, "miz");
    let sev = match severity {
      Severity::Error => "error",
      Severity::Warning => "warning",
    };
    eprintln!("{}:{pos:?}: {sev}: {msg}", file.to_string_lossy());
    severity == Severity::Error
  }
}
