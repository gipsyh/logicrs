use crate::{DagCnf, Lit, LitVec, LitVvec, Var, VarVMap};
use giputils::hash::GHashSet;
use std::{
    iter::once,
    ops::{Deref, DerefMut},
};

#[derive(Debug, Clone)]
pub struct Cnf {
    max_var: Var,
    cls: Vec<LitVec>,
}

impl Cnf {
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn max_var(&self) -> Var {
        self.max_var
    }

    #[inline]
    pub fn new_var(&mut self) -> Var {
        self.max_var += 1;
        self.max_var
    }

    #[inline]
    pub fn new_var_to(&mut self, n: Var) {
        self.max_var = self.max_var.max(n);
    }

    #[inline]
    pub fn add_clause(&mut self, cls: &[Lit]) {
        if let Some(m) = cls.iter().map(|l| l.var()).max() {
            self.max_var = self.max_var.max(m);
        }
        self.cls.push(LitVec::from(cls));
    }

    #[inline]
    pub fn add_clauses(&mut self, cls: impl IntoIterator<Item = impl AsRef<LitVec>>) {
        for cls in cls {
            self.add_clause(cls.as_ref());
        }
    }

    #[inline]
    pub fn clauses(&self) -> &[LitVec] {
        &self.cls
    }

    pub fn rearrange(&mut self, additional: impl IntoIterator<Item = impl AsRef<Var>>) -> VarVMap {
        let mut domain = GHashSet::from_iter(
            additional
                .into_iter()
                .map(|l| *l.as_ref())
                .chain(once(Var::CONST)),
        );
        for cls in self.cls.iter() {
            for l in cls.iter() {
                domain.insert(l.var());
            }
        }
        let mut domain = Vec::from_iter(domain);
        domain.sort();
        let mut domain_map = VarVMap::new();
        for (i, d) in domain.iter().enumerate() {
            domain_map.insert(*d, Var::new(i));
        }
        let map_lit = |l: &Lit| l.map_var(|v| domain_map[v]);
        for cls in self.cls.iter_mut() {
            for l in cls.iter_mut() {
                *l = map_lit(l);
            }
        }
        self.max_var = Var::new(domain.len() - 1);
        domain_map
    }

    pub fn set_cls(&mut self, cls: Vec<LitVec>) {
        self.cls = cls;
    }

    #[inline]
    pub fn new_and(&mut self, ands: impl IntoIterator<Item = impl AsRef<Lit>>) -> Lit {
        let mut and = Vec::new();
        for a in ands.into_iter() {
            let a = a.as_ref();
            if a.is_constant(true) {
                continue;
            }
            if a.is_constant(false) {
                return Lit::constant(false);
            }
            and.push(*a);
        }
        if and.is_empty() {
            Lit::constant(true)
        } else if and.len() == 1 {
            and[0]
        } else {
            let n = self.new_var().lit();
            self.add_clauses(LitVvec::cnf_and(n, &and));
            n
        }
    }

    #[inline]
    pub fn new_or(&mut self, ors: impl IntoIterator<Item = impl AsRef<Lit>>) -> Lit {
        let mut or = Vec::new();
        for o in ors.into_iter() {
            let o = o.as_ref();
            if o.is_constant(false) {
                continue;
            }
            if o.is_constant(true) {
                return Lit::constant(true);
            }
            or.push(*o);
        }
        if or.is_empty() {
            Lit::constant(false)
        } else if or.len() == 1 {
            or[0]
        } else {
            let n = self.new_var().lit();
            self.add_clauses(LitVvec::cnf_or(n, &or));
            n
        }
    }
}

impl Deref for Cnf {
    type Target = [LitVec];

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.cls
    }
}

impl DerefMut for Cnf {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.cls
    }
}

impl Default for Cnf {
    fn default() -> Self {
        Self {
            max_var: Var(0),
            cls: vec![LitVec::from([Lit::constant(true)])],
        }
    }
}

impl DagCnf {
    #[inline]
    pub fn lower(&self) -> Cnf {
        Cnf {
            max_var: self.max_var(),
            cls: self.clause().cloned().collect(),
        }
    }
}
