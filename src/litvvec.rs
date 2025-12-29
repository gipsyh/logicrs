use crate::{Lit, LitVec};
use serde::{Deserialize, Serialize};
use std::{
    ops::{Deref, DerefMut},
    slice, vec,
};

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct LitVvec {
    vec: Vec<LitVec>,
}

impl LitVvec {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn cnf_and(n: Lit, lits: &[Lit]) -> Self {
        let mut vec = Vec::new();
        let mut cls = LitVec::from([n]);
        for l in lits.iter() {
            vec.push(LitVec::from([!n, *l]));
            cls.push(!*l);
        }
        vec.push(cls);
        Self { vec }
    }

    #[inline]
    pub fn cnf_or(n: Lit, lits: &[Lit]) -> Self {
        let mut vec = Vec::new();
        let mut cls = LitVec::from([!n]);
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
        self.sort_by_key(|l| l.len());
        for c in self.iter_mut() {
            c.sort();
        }
        let mut i = 0;
        while i < self.len() {
            if self[i].is_empty() {
                i += 1;
                continue;
            }
            let mut update = false;
            for j in 0..self.len() {
                if i == j {
                    continue;
                }
                if self[j].is_empty() {
                    continue;
                }
                let (res, diff) = self[i].ordered_subsume_execpt_one(&self[j]);
                if res {
                    self[j] = Default::default();
                    continue;
                } else if let Some(diff) = diff {
                    if self[i].len() == self[j].len() {
                        update = true;
                        self[i].retain(|l| *l != diff);
                        self[j] = Default::default();
                    } else {
                        self[j].retain(|l| *l != !diff);
                    }
                }
            }
            if !update {
                i += 1;
            }
        }
        self.retain(|l| !l.is_empty());
    }
}

impl Deref for LitVvec {
    type Target = Vec<LitVec>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.vec
    }
}

impl DerefMut for LitVvec {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.vec
    }
}

impl IntoIterator for LitVvec {
    type Item = LitVec;
    type IntoIter = vec::IntoIter<LitVec>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.vec.into_iter()
    }
}

impl<'a> IntoIterator for &'a LitVvec {
    type Item = &'a LitVec;
    type IntoIter = slice::Iter<'a, LitVec>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.vec.iter()
    }
}

impl FromIterator<LitVec> for LitVvec {
    #[inline]
    fn from_iter<T: IntoIterator<Item = LitVec>>(iter: T) -> Self {
        Self {
            vec: Vec::from_iter(iter),
        }
    }
}
