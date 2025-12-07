use crate::{DagCnf, Lit, LitVec, Var, VarVMap};
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
