use crate::{Lit, Var, VarAssign};
use giputils::hash::GHashSet;
use std::{
    cmp::Ordering,
    fmt::{self, Debug, Display},
    ops::{Deref, DerefMut, Not},
    slice,
};

#[derive(Clone, Hash, PartialEq, Eq)]
pub struct LitVec {
    lits: Vec<Lit>,
}

impl LitVec {
    #[inline]
    pub fn new() -> Self {
        LitVec { lits: Vec::new() }
    }

    #[inline]
    pub fn new_with_cap(c: usize) -> Self {
        LitVec {
            lits: Vec::with_capacity(c),
        }
    }

    #[inline]
    pub fn last(&self) -> Lit {
        #[cfg(debug_assertions)]
        {
            self.lits.last().copied().unwrap()
        }
        #[cfg(not(debug_assertions))]
        unsafe {
            self.lits.last().copied().unwrap_unchecked()
        }
    }

    #[inline]
    pub fn ordered_simp(&self, v: &VarAssign) -> Option<Self> {
        let mut res = LitVec::new_with_cap(self.len());
        for i in 0..self.len() {
            let lv = v.v(self[i]);
            if lv.is_true() {
                return None;
            } else if lv.is_false() {
                continue;
            }
            if let Some(&last) = (*res).last() {
                if self[i] == last {
                    continue;
                } else if self[i] == !last {
                    return None;
                }
            }
            res.push(self[i]);
        }
        Some(res)
    }

    #[inline]
    pub fn subsume(&self, o: &[Lit]) -> bool {
        if self.len() > o.len() {
            return false;
        }
        'n: for x in self.iter() {
            for y in o.iter() {
                if x == y {
                    continue 'n;
                }
            }
            return false;
        }
        true
    }

    pub fn subsume_execpt_one(&self, o: &[Lit]) -> (bool, Option<Lit>) {
        if self.len() > o.len() {
            return (false, None);
        }
        let mut diff = None;
        'n: for x in self.iter() {
            for y in o.iter() {
                if x == y {
                    continue 'n;
                }
                if diff.is_none() && x.var() == y.var() {
                    diff = Some(*x);
                    continue 'n;
                }
            }
            return (false, None);
        }

        (diff.is_none(), diff)
    }

    #[inline]
    pub fn ordered_subsume(&self, cube: &LitVec) -> bool {
        debug_assert!(self.is_sorted());
        debug_assert!(cube.is_sorted());
        if self.len() > cube.len() {
            return false;
        }
        let mut j = 0;
        for i in 0..self.len() {
            while j < cube.len() && self[i].0 > cube[j].0 {
                j += 1;
            }
            if j == cube.len() || self[i] != cube[j] {
                return false;
            }
        }
        true
    }

    #[inline]
    pub fn ordered_subsume_execpt_one(&self, cube: &LitVec) -> (bool, Option<Lit>) {
        debug_assert!(self.is_sorted());
        debug_assert!(cube.is_sorted());
        let mut diff = None;
        if self.len() > cube.len() {
            return (false, None);
        }
        let mut j = 0;
        for i in 0..self.len() {
            while j < cube.len() && self[i].var() > cube[j].var() {
                j += 1;
            }
            if j == cube.len() {
                return (false, None);
            }
            if self[i] != cube[j] {
                if diff.is_none() && self[i].var() == cube[j].var() {
                    diff = Some(self[i]);
                } else {
                    return (false, None);
                }
            }
        }
        (diff.is_none(), diff)
    }

    #[inline]
    pub fn intersection(&self, cube: &LitVec) -> LitVec {
        let x_lit_set = self.iter().collect::<GHashSet<&Lit>>();
        let y_lit_set = cube.iter().collect::<GHashSet<&Lit>>();
        Self {
            lits: x_lit_set
                .intersection(&y_lit_set)
                .copied()
                .copied()
                .collect(),
        }
    }

    #[inline]
    pub fn ordered_intersection(&self, cube: &LitVec) -> LitVec {
        debug_assert!(self.is_sorted());
        debug_assert!(cube.is_sorted());
        let mut res = LitVec::new();
        let mut i = 0;
        for l in self.iter() {
            while i < cube.len() && cube[i] < *l {
                i += 1;
            }
            if i == cube.len() {
                break;
            }
            if *l == cube[i] {
                res.push(*l);
            }
        }
        res
    }

    #[inline]
    pub fn resolvent(&self, other: &LitVec, v: Var) -> Option<LitVec> {
        let (x, y) = if self.len() < other.len() {
            (self, other)
        } else {
            (other, self)
        };
        let mut new = LitVec::new();
        'n: for x in x.iter() {
            if x.var() != v {
                for y in y.iter() {
                    if x.var() == y.var() {
                        if *x == !*y {
                            return None;
                        } else {
                            continue 'n;
                        }
                    }
                }
                new.push(*x);
            }
        }
        new.extend(y.iter().filter(|l| l.var() != v).copied());
        Some(new)
    }

    #[inline]
    pub fn ordered_resolvent(&self, other: &LitVec, v: Var) -> Option<LitVec> {
        debug_assert!(self.is_sorted());
        debug_assert!(other.is_sorted());
        let (x, y) = if self.len() < other.len() {
            (self, other)
        } else {
            (other, self)
        };
        let mut new = LitVec::new_with_cap(self.len() + other.len());
        let (mut i, mut j) = (0, 0);
        while i < x.len() {
            if x[i].var() == v {
                i += 1;
                continue;
            }
            while j < y.len() && y[j].var() < x[i].var() {
                j += 1;
            }
            if j < y.len() && x[i].var() == y[j].var() {
                if x[i] == !y[j] {
                    return None;
                }
            } else {
                new.push(x[i]);
            }
            i += 1;
        }
        new.extend(y.iter().filter(|l| l.var() != v).copied());
        Some(new)
    }

    #[inline]
    pub fn map_var(&self, f: impl Fn(Var) -> Var) -> LitVec {
        let mut new = LitVec::new_with_cap(self.len());
        for l in self.iter() {
            new.push(l.map_var(&f));
        }
        new
    }

    #[inline]
    pub fn filter_map_var(&self, f: impl Fn(Var) -> Option<Var>) -> LitVec {
        let mut new = LitVec::new_with_cap(self.len());
        for l in self.iter() {
            if let Some(l) = l.filter_map_var(&f) {
                new.push(l);
            }
        }
        new
    }

    #[inline]
    pub fn map(&self, f: impl Fn(Lit) -> Lit) -> LitVec {
        let mut new = LitVec::new_with_cap(self.len());
        for l in self.iter() {
            new.push(f(*l));
        }
        new
    }

    #[inline]
    pub fn filter_map(&self, f: impl Fn(Lit) -> Option<Lit>) -> LitVec {
        let mut new = LitVec::new_with_cap(self.len());
        for &l in self.iter() {
            if let Some(l) = f(l) {
                new.push(l);
            }
        }
        new
    }
}

impl Default for LitVec {
    fn default() -> Self {
        Self::new()
    }
}

impl Deref for LitVec {
    type Target = Vec<Lit>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.lits
    }
}

impl DerefMut for LitVec {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.lits
    }
}

impl PartialOrd for LitVec {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for LitVec {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        debug_assert!(self.is_sorted());
        debug_assert!(other.is_sorted());
        let min_index = self.len().min(other.len());
        for i in 0..min_index {
            match self[i].0.cmp(&other[i].0) {
                Ordering::Less => return Ordering::Less,
                Ordering::Equal => {}
                Ordering::Greater => return Ordering::Greater,
            }
        }
        self.len().cmp(&other.len())
    }
}

impl Not for LitVec {
    type Output = LitVec;

    #[inline]
    fn not(self) -> Self::Output {
        let lits = self.lits.iter().map(|lit| !*lit).collect();
        LitVec { lits }
    }
}

impl Not for &LitVec {
    type Output = LitVec;

    #[inline]
    fn not(self) -> Self::Output {
        let lits = self.lits.iter().map(|lit| !*lit).collect();
        LitVec { lits }
    }
}

impl<const N: usize> From<[Lit; N]> for LitVec {
    #[inline]
    fn from(s: [Lit; N]) -> Self {
        Self { lits: Vec::from(s) }
    }
}

impl From<Lit> for LitVec {
    #[inline]
    fn from(l: Lit) -> Self {
        Self { lits: vec![l] }
    }
}

impl From<&[Lit]> for LitVec {
    #[inline]
    fn from(s: &[Lit]) -> Self {
        Self { lits: Vec::from(s) }
    }
}

impl From<&LitVec> for LitVec {
    #[inline]
    fn from(s: &LitVec) -> Self {
        s.clone()
    }
}

impl From<LitVec> for Vec<Lit> {
    #[inline]
    fn from(val: LitVec) -> Self {
        val.lits
    }
}

impl FromIterator<Lit> for LitVec {
    #[inline]
    fn from_iter<T: IntoIterator<Item = Lit>>(iter: T) -> Self {
        Self {
            lits: Vec::from_iter(iter),
        }
    }
}

impl IntoIterator for LitVec {
    type Item = Lit;
    type IntoIter = std::vec::IntoIter<Lit>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.lits.into_iter()
    }
}

impl<'a> IntoIterator for &'a LitVec {
    type Item = &'a Lit;
    type IntoIter = slice::Iter<'a, Lit>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.lits.iter()
    }
}

impl AsRef<[Lit]> for LitVec {
    #[inline]
    fn as_ref(&self) -> &[Lit] {
        self.as_slice()
    }
}

impl Display for LitVec {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.lits.fmt(f)
    }
}

impl Debug for LitVec {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.lits.fmt(f)
    }
}
