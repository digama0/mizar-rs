use std::cmp::Ordering;
use std::fmt::{Debug, Display};

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Rational {
  num: i32,
  den: u32, // Invariant: positive
}
impl Default for Rational {
  fn default() -> Self { Self::ZERO }
}

impl Display for Rational {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if self.den == 1 {
      write!(f, "{}", self.num)
    } else {
      write!(f, "{}/{}", self.num, self.den)
    }
  }
}

fn gcd(mut a: u32, mut b: u32) -> u32 {
  if a >= b {
    std::mem::swap(&mut a, &mut b)
  }
  loop {
    match a {
      0 => return b,
      _ => (a, b) = (b % a, a),
    }
  }
}

impl Rational {
  pub const fn int(num: i32) -> Self { Self { num, den: 1 } }
  pub const ZERO: Self = Self::int(0);
  pub const ONE: Self = Self::int(1);
  pub const NEG_ONE: Self = Self::int(-1);
}

impl std::ops::Add for Rational {
  type Output = Result<Self, ()>;
  fn add(self, rhs: Self) -> Self::Output {
    let g = gcd(self.den, rhs.den);
    Ok(if g == 1 {
      Self {
        num: (self.num as i64 * rhs.den as i64 + rhs.num as i64 * self.den as i64)
          .try_into()
          .map_err(|_| ())?,
        den: self.den.checked_mul(rhs.den).ok_or(())?,
      }
    } else {
      let den = (self.den / g) as i64 * rhs.den as i64;
      let num = (self.num as i64) * (rhs.den / g) as i64 + rhs.num as i64 * (self.den / g) as i64;
      let g1 = gcd((num.abs() % g as i64) as u32, g);
      if g1 == 1 {
        Self { num: num.try_into().map_err(|_| ())?, den: den.try_into().map_err(|_| ())? }
      } else {
        Self {
          num: (num / g1 as i64).try_into().map_err(|_| ())?,
          den: (den / g1 as i64).try_into().map_err(|_| ())?,
        }
      }
    })
  }
}

impl std::ops::Neg for Rational {
  type Output = Result<Self, ()>;
  fn neg(self) -> Self::Output {
    Ok(Self { num: self.num.checked_neg().ok_or(())?, den: self.den })
  }
}

impl std::ops::Sub for Rational {
  type Output = Result<Self, ()>;
  fn sub(self, rhs: Self) -> Self::Output { self + (-rhs)? }
}

impl std::ops::Mul for Rational {
  type Output = Result<Self, ()>;
  fn mul(self, rhs: Self) -> Self::Output {
    let g1 = gcd(self.num.unsigned_abs(), rhs.den);
    let g2 = gcd(rhs.num.unsigned_abs(), self.den);
    Ok(Self {
      num: ((self.num as i64 / g1 as i64) * (rhs.num as i64 / g2 as i64))
        .try_into()
        .map_err(|_| ())?,
      den: ((self.den as i64 / g2 as i64) * (rhs.den as i64 / g1 as i64))
        .try_into()
        .map_err(|_| ())?,
    })
  }
}

impl Rational {
  pub fn inv(self) -> Result<Self, ()> {
    match self.num.cmp(&0) {
      Ordering::Less => Ok(Self {
        num: (-(self.den as i64)).try_into().map_err(|_| ())?,
        den: -(self.num as i64) as u32,
      }),
      Ordering::Equal => Err(()),
      Ordering::Greater =>
        Ok(Self { num: self.den.try_into().map_err(|_| ())?, den: self.num as u32 }),
    }
  }
}

impl std::ops::Div for Rational {
  type Output = Result<Self, ()>;
  #[allow(clippy::suspicious_arithmetic_impl)]
  fn div(self, rhs: Self) -> Self::Output { self * rhs.inv()? }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Default)]
pub struct Complex {
  re: Rational,
  im: Rational,
}

impl Display for Complex {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if self.im == Rational::ZERO {
      self.re.fmt(f)
    } else if self.re == Rational::ZERO {
      write!(f, "{}i", self.im)
    } else {
      write!(f, "{}+{}i", self.re, self.im)
    }
  }
}

impl Debug for Complex {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "{self}") }
}

impl Complex {
  pub const fn real(re: Rational) -> Self { Self { re, im: Rational::ZERO } }
  // TODO: this should be infallible
  pub fn int(num: u32) -> Self { Self::real(Rational::int(num.try_into().unwrap())) }
  pub const ZERO: Self = Self::real(Rational::ZERO);
  pub const ONE: Self = Self::real(Rational::ONE);
  pub const NEG_ONE: Self = Self::real(Rational::NEG_ONE);
  pub const I: Self = Self { re: Rational::ZERO, im: Rational::ONE };

  pub fn pow(mut self, n: u32) -> Result<Self, ()> {
    match n {
      0 => Ok(Complex::ONE),
      1 => Ok(self),
      _ => {
        let a = self.clone();
        for i in (0..n.ilog2()).rev() {
          self = (self.clone() * self)?;
          if (n >> i) & 1 != 0 {
            self = (self * a.clone())?;
          }
        }
        Ok(self)
      }
    }
  }
}
impl From<Rational> for Complex {
  fn from(value: Rational) -> Self { Self::real(value) }
}
impl From<u32> for Complex {
  fn from(value: u32) -> Self { Self::int(value) }
}

impl std::ops::Add for Complex {
  type Output = Result<Self, ()>;
  fn add(self, rhs: Self) -> Self::Output {
    Ok(Self { re: (self.re + rhs.re)?, im: (self.im + rhs.im)? })
  }
}

impl std::ops::Neg for Complex {
  type Output = Result<Self, ()>;
  fn neg(self) -> Self::Output { Ok(Self { re: (-self.re)?, im: (-self.im)? }) }
}

impl std::ops::Sub for Complex {
  type Output = Result<Self, ()>;
  fn sub(self, rhs: Self) -> Self::Output {
    Ok(Self { re: (self.re - rhs.re)?, im: (self.im - rhs.im)? })
  }
}

impl std::ops::Mul for Complex {
  type Output = Result<Self, ()>;
  fn mul(self, rhs: Self) -> Self::Output {
    Ok(Self {
      re: ((self.re.clone() * rhs.re.clone())? - (self.im.clone() * rhs.im.clone())?)?,
      im: ((self.re * rhs.im)? + (rhs.re * self.im)?)?,
    })
  }
}

impl Complex {
  pub fn inv(self) -> Result<Self, ()> {
    let d = ((self.re.clone() * self.re.clone())? + (self.im.clone() * self.im.clone())?)?.inv()?;
    Ok(Self { re: (self.re * d.clone())?, im: ((-self.im)? * d)? })
  }
}

impl std::ops::Div for Complex {
  type Output = Result<Self, ()>;
  #[allow(clippy::suspicious_arithmetic_impl)]
  fn div(self, rhs: Self) -> Self::Output { self * rhs.inv()? }
}
