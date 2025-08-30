pub mod simplify;
pub mod simulate;
mod top;

use crate::{Lit, LitVec, LitVvec, Var, VarLMap, VarMap, VarVMap};
use giputils::hash::GHashSet;
use std::{
    fmt::Display,
    iter::{Flatten, Zip, once},
    ops::{Index, RangeInclusive},
    slice,
};

#[derive(Debug, Clone)]
pub struct DagCnf {
    max_var: Var,
    cnf: VarMap<LitVvec>,
    dep: VarMap<Vec<Var>>,
}

impl DagCnf {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn new_var(&mut self) -> Var {
        self.max_var += 1;
        self.dep.reserve(self.max_var);
        self.cnf.reserve(self.max_var);
        self.max_var
    }

    #[inline]
    pub fn new_var_to(&mut self, n: Var) {
        while self.max_var < n {
            self.new_var();
        }
    }

    #[inline]
    pub fn max_var(&self) -> Var {
        self.max_var
    }

    #[inline]
    pub fn num_var(&self) -> usize {
        let n: usize = self.max_var().into();
        n + 1
    }

    #[inline]
    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.clause().count()
    }

    #[inline]
    pub fn var_iter(&self) -> RangeInclusive<Var> {
        Var::CONST..=self.max_var
    }

    /// var iter wo const
    #[inline]
    pub fn var_iter_woc(&self) -> RangeInclusive<Var> {
        Var(1)..=self.max_var
    }

    #[inline]
    pub fn num_clause(&self) -> usize {
        self.cnf.iter().map(|v| v.len()).sum()
    }

    #[inline]
    pub fn clause(&self) -> Flatten<slice::Iter<'_, LitVvec>> {
        self.cnf.iter().flatten()
    }

    #[inline]
    pub fn dep(&self, n: Var) -> &[Var] {
        &self.dep[n]
    }

    #[inline]
    pub fn iter(&self) -> Zip<RangeInclusive<Var>, std::slice::Iter<'_, LitVvec>> {
        (Var::CONST..=self.max_var).zip(self.cnf.iter())
    }

    #[inline]
    pub fn add_rel(&mut self, n: Var, rel: &[LitVec]) {
        self.new_var_to(n);
        if n.is_constant() {
            assert!(rel.eq(&[LitVec::from(Lit::constant(true))]));
            return;
        }
        assert!(self.dep[n].is_empty() && self.cnf[n].is_empty());
        for mut r in rel.iter().cloned() {
            r.sort();
            assert!(r.last().var() == n);
            self.cnf[n].push(r);
        }
        self.dep[n] = deps(n, &self.cnf[n]);
    }

    #[inline]
    pub fn set_rel(&mut self, n: Var, rel: &[LitVec]) {
        self.new_var_to(n);
        self.dep[n].clear();
        self.cnf[n].clear();
        self.add_rel(n, rel);
    }

    #[inline]
    pub fn del_rel(&mut self, n: Var) {
        self.dep[n].clear();
        self.cnf[n].clear();
    }

    #[inline]
    pub fn has_rel(&self, n: Var) -> bool {
        n.is_constant() || !self.cnf[n].is_empty()
    }

    #[inline]
    pub fn is_leaf(&self, n: Var) -> bool {
        self.cnf[n].is_empty()
    }

    #[inline]
    pub fn new_and(&mut self, ands: impl IntoIterator<Item = Lit>) -> Lit {
        let ands: Vec<_> = ands.into_iter().collect();
        if ands.is_empty() {
            Lit::constant(true)
        } else if ands.len() == 1 {
            ands[0]
        } else {
            let n = self.new_var().lit();
            self.add_rel(n.var(), &LitVvec::cnf_and(n, &ands));
            n
        }
    }

    #[inline]
    pub fn new_or(&mut self, ors: impl IntoIterator<Item = Lit>) -> Lit {
        let ors: Vec<_> = ors.into_iter().collect();
        if ors.is_empty() {
            Lit::constant(false)
        } else if ors.len() == 1 {
            ors[0]
        } else {
            let n = self.new_var().lit();
            self.add_rel(n.var(), &LitVvec::cnf_or(n, &ors));
            n
        }
    }

    #[inline]
    pub fn new_xor(&mut self, x: Lit, y: Lit) -> Lit {
        let n = self.new_var().lit();
        self.add_rel(n.var(), &LitVvec::cnf_xor(n, x, y));
        n
    }

    #[inline]
    pub fn new_xnor(&mut self, x: Lit, y: Lit) -> Lit {
        let n = self.new_var().lit();
        self.add_rel(n.var(), &LitVvec::cnf_xnor(n, x, y));
        n
    }

    #[inline]
    pub fn new_imply(&mut self, x: Lit, y: Lit) -> Lit {
        let n = self.new_var().lit();
        self.add_rel(n.var(), &LitVvec::cnf_or(n, &[!x, y]));
        n
    }

    #[inline]
    pub fn new_ite(&mut self, c: Lit, t: Lit, e: Lit) -> Lit {
        let n = self.new_var().lit();
        self.add_rel(n.var(), &LitVvec::cnf_ite(n, c, t, e));
        n
    }

    pub fn fanins(&self, var: impl Iterator<Item = Var>) -> GHashSet<Var> {
        let mut marked = GHashSet::new();
        let mut queue = vec![];
        for v in var {
            marked.insert(v);
            queue.push(v);
        }
        while let Some(v) = queue.pop() {
            for d in self.dep[v].iter() {
                if !marked.contains(d) {
                    marked.insert(*d);
                    queue.push(*d);
                }
            }
        }
        marked
    }

    pub fn fanouts(&self, var: impl Iterator<Item = Var>) -> GHashSet<Var> {
        let mut marked = GHashSet::from_iter(var);
        for v in Var::CONST..=self.max_var {
            if self.dep[v].iter().any(|d| marked.contains(d)) {
                marked.insert(v);
            }
        }
        marked
    }

    pub fn root(&self) -> GHashSet<Var> {
        let mut root = GHashSet::from_iter(
            (Var::new(0)..=self.max_var()).filter(|v| !self.dep[*v].is_empty()),
        );
        for d in self.dep.iter() {
            for d in d.iter() {
                root.remove(d);
            }
        }
        root
    }

    pub fn pol_filter(&mut self, pol: impl IntoIterator<Item = Lit>) {
        for p in pol {
            self.cnf[p.var()].retain(|cls| cls.last() != !p);
            self.dep[p.var()] = deps(p.var(), &self.cnf[p.var()]);
        }
    }

    pub fn rearrange(&mut self, additional: impl Iterator<Item = Var>) -> VarVMap {
        let mut domain = GHashSet::from_iter(additional.chain(once(Var::CONST)));
        for cls in self.clause() {
            for l in cls.iter() {
                domain.insert(l.var());
            }
        }
        let mut domain = Vec::from_iter(domain);
        domain.sort();
        let mut domain_map = VarVMap::new();
        let mut res = DagCnf::new();
        for (i, d) in domain.iter().enumerate() {
            let v = Var::new(i);
            res.new_var_to(v);
            domain_map.insert(*d, v);
        }
        let map_lit = |l: &Lit| l.map_var(|v| domain_map[v]);
        for (d, v) in domain_map.iter() {
            if d.is_constant() {
                continue;
            }
            let mut new_cls = Vec::new();
            for cls in self.cnf[*d].iter() {
                new_cls.push(cls.iter().map(map_lit).collect());
            }
            res.add_rel(*v, &new_cls);
        }
        *self = res;
        domain_map
    }

    pub fn map(&self, map: impl Fn(Var) -> Var) -> Self {
        assert!(map(Var::CONST) == Var::CONST);
        let mut res = DagCnf::new();
        for (v, rel) in self.iter() {
            let new_cls: Vec<_> = rel.iter().map(|cls| cls.map(|l| l.map_var(&map))).collect();
            res.add_rel(map(v), &new_cls);
        }
        res
    }

    pub fn replace(&mut self, map: &VarLMap) {
        for (old, new) in map.iter() {
            assert!(*old > new.var());
        }

        for v in Var::CONST..=self.max_var {
            if map.contains_key(&v) {
                self.cnf[v].clear();
                self.dep[v].clear();
            }
            for cls in self.cnf[v].iter_mut() {
                for l in cls.iter_mut() {
                    if let Some(new) = map.map_lit(*l) {
                        *l = new;
                    }
                }
            }
            for d in self.dep[v].iter_mut() {
                if let Some(new) = map.map(*d) {
                    *d = new.var();
                }
            }
        }
    }

    pub fn migrate(&mut self, other: &DagCnf, t: Var, map: &mut VarVMap) {
        if map.get(&t).is_some() {
            return;
        }
        for rel in other[t].iter() {
            for &l in rel.iter() {
                if l.var() != t {
                    self.migrate(other, l.var(), map);
                }
            }
        }
        let n = self.new_var();
        map.insert(t, n);
        let mut new_rel = Vec::new();
        for rel in other[t].iter() {
            new_rel.push(rel.map(|l| map.lit_map(l).unwrap()));
        }
        self.add_rel(n, &new_rel);
    }
}

impl Default for DagCnf {
    fn default() -> Self {
        let max_var = Var::CONST;
        let mut cnf: VarMap<LitVvec> = VarMap::new_with(max_var);
        cnf[max_var].push(LitVec::from(Lit::constant(true)));
        Self {
            max_var,
            cnf,
            dep: VarMap::new_with(max_var),
        }
    }
}

impl Index<Var> for DagCnf {
    type Output = [LitVec];

    #[inline]
    fn index(&self, index: Var) -> &Self::Output {
        &self.cnf[index]
    }
}

impl Display for DagCnf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for cls in self.clause() {
            writeln!(f, "{cls}")?;
        }
        Ok(())
    }
}

#[inline]
fn deps(n: Var, cnf: &[LitVec]) -> Vec<Var> {
    let mut dep = GHashSet::new();
    for cls in cnf.iter() {
        for l in cls.iter() {
            dep.insert(l.var());
        }
    }
    dep.remove(&n);
    dep.into_iter().collect()
}
