use super::Equals;
use crate::bignum::{Complex, Rational};
use crate::checker::OrUnsat;
use crate::equate::Equalizer;
use crate::types::*;
use itertools::{EitherOrBoth, Itertools};
use std::cmp::Ordering;
use std::collections::BTreeMap;

#[derive(Clone)]
pub struct Monomial {
  /// invariant: not zero inside polynomial
  coeff: Complex,
  /// invariant: map does not contain zero powers
  powers: BTreeMap<EqTermId, u32>,
}

impl std::fmt::Debug for Monomial {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut strs = vec![];
    if self.coeff != Complex::ONE {
      if self.coeff.im != Rational::ZERO {
        strs.push(format!("({})", self.coeff))
      } else {
        strs.push(format!("{}", self.coeff))
      }
    }
    for (&et, &k) in &self.powers {
      if k == 1 {
        strs.push(format!("x{et:?}"))
      } else {
        strs.push(format!("x{et:?}^{k}"))
      }
    }
    if strs.is_empty() {
      write!(f, "1")
    } else {
      write!(f, "{}", strs.iter().format("*"))
    }
  }
}

// This ignores the coefficients
impl Ord for Monomial {
  fn cmp(&self, other: &Self) -> Ordering {
    self.degree().cmp(&other.degree()).then_with(|| {
      self.powers.len().cmp(&other.powers.len()).then_with(|| self.powers.cmp(&other.powers))
    })
  }
}
impl PartialOrd for Monomial {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}
impl PartialEq for Monomial {
  fn eq(&self, other: &Self) -> bool { self.cmp(other) == Ordering::Equal }
}
impl Eq for Monomial {}

impl Monomial {
  pub const fn cnst(coeff: Complex) -> Self { Self { coeff, powers: BTreeMap::new() } }
  pub fn atom(var: EqTermId) -> Self {
    Self { coeff: Complex::ONE, powers: std::iter::once((var, 1)).collect() }
  }
  pub fn degree(&self) -> u32 { self.powers.iter().map(|p| p.1).sum() }

  fn mul(&self, other: &Self) -> Self {
    let coeff = self.coeff.clone() * other.coeff.clone();
    let mut powers = BTreeMap::new();
    for item in self.powers.iter().merge_join_by(&other.powers, |a, b| a.0.cmp(b.0)) {
      match item {
        EitherOrBoth::Left((&et, &n)) | EitherOrBoth::Right((&et, &n)) => powers.insert(et, n),
        EitherOrBoth::Both((&et, &n1), (_, &n2)) => powers.insert(et, n1.checked_add(n2).unwrap()),
      };
    }
    Monomial { coeff, powers }
  }

  fn lex(&self, other: &Self) -> Ordering {
    self.powers.iter().map(|p| (p.0, !*p.1)).cmp(other.powers.iter().map(|p| (p.0, !*p.1)))
  }

  pub fn contains(&self, et: EqTermId) -> bool { self.powers.contains_key(&et) }

  pub fn is_var(&self) -> Option<EqTermId> {
    if self.powers.len() != 1 || self.coeff != Complex::ONE {
      return None
    }
    match self.powers.first_key_value() {
      Some((&et, 1)) => Some(et),
      _ => None,
    }
  }

  pub fn is_const(&self) -> Option<Complex> {
    if self.powers.is_empty() {
      Some(self.coeff.clone())
    } else {
      None
    }
  }

  /// * Returns `Some(Some(v))` if the monomial is univariate in `v`
  /// * Returns `Some(None)` if the monomial is a constant
  /// * Returns `None` if the monomial uses two or more variables
  pub fn is_univariate(&self) -> Option<Option<EqTermId>> {
    match self.powers.len() {
      0 => Some(None),
      1 => Some(Some(*self.powers.first_key_value().unwrap().0)),
      _ => None,
    }
  }

  pub fn pow(&mut self, n: u32) {
    match n {
      0 => *self = Monomial::cnst(Complex::ONE),
      1 => {}
      _ => {
        self.coeff = std::mem::take(&mut self.coeff).pow(n.into());
        for i in self.powers.values_mut() {
          *i = i.checked_mul(n).unwrap();
        }
      }
    }
  }
}

#[derive(Clone)]
pub struct Polynomial(
  /// sorted by Monomial::lex
  Vec<Monomial>,
);

impl std::fmt::Debug for Polynomial {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if self.0.is_empty() {
      write!(f, "poly 0")
    } else {
      write!(f, "poly {:?}", self.0.iter().format(" + "))
    }
  }
}

impl Ord for Polynomial {
  fn cmp(&self, other: &Self) -> Ordering {
    self.0.len().cmp(&other.0.len()).then_with(|| {
      for (a, b) in self.0.iter().zip(&other.0) {
        match a.cmp(b).then_with(|| a.coeff.cmp(&b.coeff)) {
          Ordering::Equal => {}
          non_eq => return non_eq,
        }
      }
      Ordering::Equal
    })
  }
}
impl PartialOrd for Polynomial {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}
impl PartialEq for Polynomial {
  fn eq(&self, other: &Self) -> bool { self.cmp(other) == Ordering::Equal }
}
impl Eq for Polynomial {}

impl Polynomial {
  pub const ZERO: Self = Self(Vec::new());

  pub fn single(mon: Monomial) -> Self {
    if mon.coeff == Complex::ZERO {
      Self(Vec::new())
    } else {
      Self(vec![mon])
    }
  }

  pub fn add(mut self, other: Polynomial) -> Polynomial {
    let mut out = Polynomial::ZERO;
    for item in self.0.into_iter().merge_join_by(other.0, Monomial::lex) {
      match item {
        EitherOrBoth::Left(mon) | EitherOrBoth::Right(mon) => out.0.push(mon),
        EitherOrBoth::Both(mut m1, m2) => {
          m1.coeff = m1.coeff + m2.coeff;
          if m1.coeff != Complex::ZERO {
            out.0.push(m1)
          }
        }
      }
    }
    out
  }

  pub fn sub(mut self, other: Polynomial) -> Polynomial { self.add(other.smul(&Complex::NEG_ONE)) }

  pub fn is_zero(&self) -> bool { self.0.is_empty() }

  fn dedup(&mut self) {
    let mut it = std::mem::take(&mut self.0).into_iter();
    if let Some(mut mon) = it.next() {
      for m2 in it {
        if mon == m2 {
          mon.coeff = mon.coeff + m2.coeff;
        } else {
          if mon.coeff != Complex::ZERO {
            self.0.push(mon)
          }
          mon = m2;
        }
      }
      if mon.coeff != Complex::ZERO {
        self.0.push(mon)
      }
    }
  }

  pub fn mul(&self, other: &Polynomial) -> Polynomial {
    if self.is_zero() || other.is_zero() {
      return Polynomial::ZERO
    }
    let mut out = Polynomial::ZERO;
    for i in &self.0 {
      for j in &other.0 {
        let mon = i.mul(j);
        out.0.push(mon)
      }
    }
    out.0.sort_unstable_by(Monomial::lex);
    out.dedup();
    out
  }

  pub fn smul(mut self, other: &Complex) -> Polynomial {
    if *other == Complex::ZERO {
      return Polynomial::ZERO
    }
    if *other == Complex::ONE {
      return self
    }
    for mon in &mut self.0 {
      mon.coeff = std::mem::take(&mut mon.coeff) * other.clone()
    }
    self
  }

  pub fn mmul(mut self, other: &Monomial) -> Polynomial {
    if other.coeff == Complex::ZERO {
      return Polynomial::ZERO
    }
    if other.is_const() == Some(Complex::ONE) {
      return self
    }
    for mon in &mut self.0 {
      mon.coeff = std::mem::take(&mut mon.coeff) * other.coeff.clone();
      for (&et, &i) in &other.powers {
        let v = mon.powers.entry(et).or_default();
        *v = v.checked_add(i).unwrap();
      }
    }
    self.0.sort_unstable_by(Monomial::lex);
    self
  }

  pub fn is_var(&self) -> Option<EqTermId> {
    match *self.0 {
      [ref mon] => mon.is_var(),
      _ => None,
    }
  }

  /// * Returns `Some(Some(v))` if the polynomial is univariate in `v`
  /// * Returns `Some(None)` if the polynomial is a constant
  /// * Returns `None` if the polynomial uses two or more variables
  pub fn is_univariate(&self) -> Option<Option<EqTermId>> {
    let mut v = None;
    for mon in &self.0 {
      if let Some(v2) = mon.is_univariate()? {
        if matches!(v.replace(v2), Some(v1) if v1 != v2) {
          return None
        }
      }
    }
    Some(v)
  }

  pub fn is_const(&self) -> Option<Complex> {
    match *self.0 {
      [] => Some(Complex::ZERO),
      [ref mon] => mon.is_const(),
      _ => None,
    }
  }

  pub fn contains(&self, et: EqTermId) -> bool { self.0.iter().any(|mon| mon.contains(et)) }

  pub fn pow(&self, n: u32) -> Polynomial {
    match n {
      0 => Polynomial::single(Monomial::cnst(Complex::ONE)),
      1 => self.clone(),
      _ => match *self.0 {
        [] => Polynomial::ZERO,
        [ref mon] => {
          let mut mon = mon.clone();
          mon.pow(n);
          Polynomial(vec![mon])
        }
        _ => {
          let mut out = self.clone();
          for i in (0..n.ilog2()).rev() {
            out = out.mul(&out);
            if (n >> i) & 1 != 0 {
              out = out.mul(self);
            }
          }
          out
        }
      },
    }
  }

  /// computes self = self[et |-> p]
  pub fn subst(&mut self, et: EqTermId, p: &Polynomial) {
    for mut mon in std::mem::take(&mut self.0) {
      if let Some(n) = mon.powers.remove(&et) {
        if !p.is_zero() {
          self.0.append(&mut p.pow(n).mmul(&mon).0);
        }
      } else {
        self.0.push(mon)
      }
    }
    self.0.sort_by(Monomial::lex);
    self.dedup()
  }
}
