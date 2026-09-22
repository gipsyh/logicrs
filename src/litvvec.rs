use crate::{Lit, LitOrdVec, LitVec, lemmas_subsume_simplify};
use serde::{Deserialize, Serialize};
use std::{
    ops::{Deref, DerefMut},
    slice, vec,
};

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct LitVvec<T = LitVec> {
    vec: Vec<T>,
}

impl LitVvec {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn cnf_and(n: Lit, lits: &[Lit]) -> Self {
        let mut vec = Vec::with_capacity(lits.len() + 1);
        let mut cls = LitVec::new_with_cap(lits.len() + 1);
        cls.push(n);
        for l in lits.iter() {
            vec.push(LitVec::from([!n, *l]));
            cls.push(!*l);
        }
        vec.push(cls);
        Self { vec }
    }

    #[inline]
    pub fn cnf_or(n: Lit, lits: &[Lit]) -> Self {
        let mut vec = Vec::with_capacity(lits.len() + 1);
        let mut cls = LitVec::new_with_cap(lits.len() + 1);
        cls.push(!n);
        for l in lits.iter() {
            vec.push(LitVec::from([n, !*l]));
            cls.push(*l);
        }
        vec.push(cls);
        Self { vec }
    }

    #[inline]
    pub fn cnf_assign(n: Lit, s: Lit) -> Self {
        Self {
            vec: vec![LitVec::from([n, !s]), LitVec::from([!n, s])],
        }
    }

    #[inline]
    pub fn cnf_xor(n: Lit, x: Lit, y: Lit) -> Self {
        Self {
            vec: vec![
                LitVec::from([!x, y, n]),
                LitVec::from([x, !y, n]),
                LitVec::from([x, y, !n]),
                LitVec::from([!x, !y, !n]),
            ],
        }
    }

    #[inline]
    pub fn cnf_xnor(n: Lit, x: Lit, y: Lit) -> Self {
        Self {
            vec: vec![
                LitVec::from([!x, y, !n]),
                LitVec::from([x, !y, !n]),
                LitVec::from([x, y, n]),
                LitVec::from([!x, !y, n]),
            ],
        }
    }

    #[inline]
    pub fn cnf_ite(n: Lit, c: Lit, t: Lit, e: Lit) -> Self {
        Self {
            vec: vec![
                LitVec::from([t, !c, !n]),
                LitVec::from([!t, !c, n]),
                LitVec::from([e, c, !n]),
                LitVec::from([!e, c, n]),
            ],
        }
    }

    pub fn subsume_simplify(&mut self) {
        let res: Vec<_> = self.iter().map(|l| LitOrdVec::new(l.clone())).collect();
        self.vec = lemmas_subsume_simplify(res)
            .into_iter()
            .map(|l| l.into_litvec())
            .collect();
    }
}

impl<T> Deref for LitVvec<T> {
    type Target = Vec<T>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.vec
    }
}

impl<T> DerefMut for LitVvec<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.vec
    }
}

impl<T> IntoIterator for LitVvec<T> {
    type Item = T;
    type IntoIter = vec::IntoIter<T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.vec.into_iter()
    }
}

impl<'a, T> IntoIterator for &'a LitVvec<T> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.vec.iter()
    }
}

impl<T> FromIterator<T> for LitVvec<T> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self {
            vec: Vec::from_iter(iter),
        }
    }
}

impl<T> From<Vec<T>> for LitVvec<T> {
    fn from(vec: Vec<T>) -> Self {
        Self { vec }
    }
}
