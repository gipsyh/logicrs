#![feature(step_trait, try_trait_v2)]

mod assign;
mod cnf;
mod cstdagcnf;
mod dagcnf;
pub mod dimacs;
pub mod fol;
mod lbool;
mod litordvec;
mod litvec;
mod litvvec;
mod occur;
pub mod satif;
mod utils;

pub use assign::*;
pub use cnf::*;
pub use cstdagcnf::*;
pub use dagcnf::*;
pub use lbool::*;
pub use litordvec::*;
pub use litvec::*;
pub use litvvec::*;
pub use utils::*;

use std::{
    fmt::{self, Debug, Display},
    hash::Hash,
    iter::Step,
    ops::{Add, AddAssign, Deref, Not, Sub},
};

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct Var(pub u32);

impl Var {
    pub const CONST: Var = Var(0);

    #[inline]
    pub fn new(x: usize) -> Self {
        Self(x as _)
    }

    #[inline]
    pub fn lit(&self) -> Lit {
        Lit(self.0 << 1)
    }

    #[inline]
    pub fn is_constant(&self) -> bool {
        *self == Self::CONST
    }
}

impl Add<Var> for Var {
    type Output = Var;

    #[inline]
    fn add(self, rhs: Var) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl AddAssign<Var> for Var {
    #[inline]
    fn add_assign(&mut self, rhs: Var) {
        self.0 += rhs.0;
    }
}

impl From<Lit> for Var {
    #[inline]
    fn from(value: Lit) -> Self {
        value.var()
    }
}

impl Deref for Var {
    type Target = u32;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl AsRef<Var> for Var {
    #[inline]
    fn as_ref(&self) -> &Var {
        self
    }
}

impl AsMut<Var> for Var {
    #[inline]
    fn as_mut(&mut self) -> &mut Var {
        self
    }
}

impl Display for Var {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Debug for Var {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Step for Var {
    #[inline]
    fn steps_between(start: &Self, end: &Self) -> (usize, Option<usize>) {
        u32::steps_between(&start.0, &end.0)
    }

    #[inline]
    fn forward_checked(start: Self, count: usize) -> Option<Self> {
        u32::forward_checked(start.0, count).map(Self)
    }

    #[inline]
    fn backward_checked(start: Self, count: usize) -> Option<Self> {
        u32::backward_checked(start.0, count).map(Self)
    }
}

macro_rules! impl_var_traits {
    ($T:ty) => {
        impl PartialEq<$T> for Var {
            #[inline]
            fn eq(&self, other: &$T) -> bool {
                self.0.eq(&(*other as u32))
            }
        }

        impl PartialOrd<$T> for Var {
            #[inline]
            fn partial_cmp(&self, other: &$T) -> Option<std::cmp::Ordering> {
                self.0.partial_cmp(&(*other as u32))
            }
        }

        impl From<Var> for $T {
            #[inline]
            fn from(value: Var) -> Self {
                value.0 as $T
            }
        }

        impl From<$T> for Var {
            #[inline]
            fn from(value: $T) -> Self {
                Self(value as u32)
            }
        }

        impl Add<$T> for Var {
            type Output = Var;

            #[inline]
            fn add(self, rhs: $T) -> Self::Output {
                Self(self.0 + rhs as u32)
            }
        }

        impl Sub<$T> for Var {
            type Output = Var;

            #[inline]
            fn sub(self, rhs: $T) -> Self::Output {
                Self(self.0 - rhs as u32)
            }
        }

        impl AddAssign<$T> for Var {
            #[inline]
            fn add_assign(&mut self, rhs: $T) {
                self.0 += rhs as u32;
            }
        }
    };
}

impl_var_traits!(u32);
impl_var_traits!(i32);
impl_var_traits!(usize);
impl_var_traits!(isize);

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct Lit(u32);

impl From<Var> for Lit {
    #[inline]
    fn from(value: Var) -> Self {
        Self(value.0 << 1)
    }
}

impl From<Lit> for u32 {
    #[inline]
    fn from(val: Lit) -> Self {
        val.0
    }
}

impl From<Lit> for i32 {
    #[inline]
    fn from(val: Lit) -> Self {
        let mut v: i32 = val.var().into();
        if !val.polarity() {
            v = -v;
        }
        v
    }
}

impl From<i32> for Lit {
    #[inline]
    fn from(value: i32) -> Self {
        Self::new(Var(value.unsigned_abs()), value > 0)
    }
}

impl Lit {
    #[inline]
    pub fn new(var: Var, polarity: bool) -> Self {
        Lit(var.0 + var.0 + !polarity as u32)
    }

    #[inline]
    pub fn var(&self) -> Var {
        Var(self.0 >> 1)
    }

    #[inline]
    pub fn polarity(&self) -> bool {
        self.0 & 1 == 0
    }

    #[inline]
    pub fn constant(polarity: bool) -> Self {
        Self::new(Var::CONST, !polarity)
    }

    #[inline]
    pub fn try_constant(&self) -> Option<bool> {
        self.var().is_constant().then_some(self.is_constant(true))
    }

    #[inline]
    pub fn is_constant(&self, polarity: bool) -> bool {
        *self == Self::constant(polarity)
    }

    #[inline]
    pub fn not_if(&self, c: bool) -> Self {
        if c { !*self } else { *self }
    }

    #[inline]
    pub fn cube(&self) -> LitVec {
        LitVec::from([*self])
    }

    #[inline]
    pub fn map_var(&self, map: impl Fn(Var) -> Var) -> Self {
        Self::new(map(self.var()), self.polarity())
    }

    #[inline]
    pub fn filter_map_var(&self, map: impl Fn(Var) -> Option<Var>) -> Option<Self> {
        map(self.var()).map(|v| Self::new(v, self.polarity()))
    }
}

impl Not for Lit {
    type Output = Self;

    #[inline]
    fn not(mut self) -> Self::Output {
        self.0 ^= 1;
        self
    }
}

impl AsRef<Lit> for Lit {
    #[inline]
    fn as_ref(&self) -> &Lit {
        self
    }
}

impl AsMut<Lit> for Lit {
    #[inline]
    fn as_mut(&mut self) -> &mut Lit {
        self
    }
}

impl Debug for Lit {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.polarity() {
            write!(f, "{}", self.var())
        } else {
            write!(f, "-{}", self.var())
        }
    }
}

impl Display for Lit {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self, f)
    }
}
