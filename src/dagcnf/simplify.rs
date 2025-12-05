use super::DagCnf;
use crate::{
    LitMap, LitOrdVec, LitVec, LitVvec, Var, VarAssign, lemmas_subsume_simplify, occur::Occurs,
};
use giputils::{allocator::Gallocator, grc::Grc, hash::GHashSet, heap::BinaryHeap};
use log::info;
use std::{
    iter::once,
    time::{Duration, Instant},
};

pub struct DagCnfSimplify {
    cdb: Grc<Gallocator<LitOrdVec>>,
    max_var: Var,
    cnf: LitMap<Vec<usize>>,
    #[allow(clippy::type_complexity)]
    occur: Option<(Grc<Occurs<LitOrdVec>>, BinaryHeap<Var, Occurs<LitOrdVec>>)>,
    frozen: GHashSet<Var>,
    value: VarAssign,
    num_ocls: usize,
    time: Duration,
}

impl DagCnfSimplify {
    pub fn new(dagcnf: &DagCnf) -> Self {
        let num_ocls = dagcnf.num_clause();
        let cdb = Grc::new(Gallocator::new());
        let max_var = dagcnf.max_var;
        let cnf = LitMap::new_with(max_var);
        let value = VarAssign::new_with(max_var);
        let mut res = Self {
            cdb,
            occur: None,
            max_var,
            cnf,
            frozen: GHashSet::from_iter([Var::CONST]),
            value,
            num_ocls,
            time: Duration::default(),
        };
        for v in Var::CONST..=max_var {
            for mut cls in dagcnf.cnf[v].clone() {
                cls.sort();
                cls.dedup();
                assert!(cls.last().var().eq(&v));
                res.add_rel(cls);
            }
        }
        res
    }

    fn enable_occur(&mut self) {
        if self.occur.is_none() {
            let mut occur = Grc::new(Occurs::new_with(self.max_var, self.cdb.clone()));
            let mut qbve = BinaryHeap::new(occur.clone());
            for v in Var::CONST..=self.max_var {
                for &cls in self.cnf[v.lit()].iter().chain(self.cnf[!v.lit()].iter()) {
                    for &l in self.cdb[cls].iter() {
                        let lv = l.var();
                        if lv != v {
                            occur.add(l, cls);
                        }
                    }
                }
            }
            for v in Var::CONST..=self.max_var {
                qbve.push(v);
            }
            self.occur = Some((occur, qbve));
        }
    }

    fn disable_occur(&mut self) {
        if self.occur.is_some() {
            self.occur = None;
        }
    }

    pub fn froze(&mut self, v: Var) {
        self.frozen.insert(v);
    }

    fn add_rel(&mut self, rel: LitVec) {
        let Some(rel) = rel.ordered_simp(&self.value) else {
            return;
        };
        let rel = LitOrdVec::new(rel);
        let n = rel.last();
        if rel.len() == 1 {
            assert!(!self.value.v(n).is_true());
            self.value.set(n);
        }
        let relid = self.cdb.alloc(rel);
        self.cnf[n].push(relid);
        if let Some((occur, qbve)) = &mut self.occur {
            for &l in self.cdb[relid].iter() {
                let lv = l.var();
                if lv != n.var() {
                    occur.add(l, relid);
                    qbve.down(lv);
                }
            }
        }
    }

    #[allow(unused)]
    fn remove_rel(&mut self, rel: usize) {
        let o = self.cdb[rel].last();
        let mut i = 0;
        while i < self.cnf[o].len() {
            if self.cnf[o][i] == rel {
                let cls = self.cnf[o].swap_remove(i);
                if let Some((occur, qbve)) = &mut self.occur {
                    for &l in self.cdb[cls].iter() {
                        let lv = l.var();
                        if lv != o.var() {
                            occur.del(l, cls);
                            qbve.up(lv);
                        }
                    }
                }
                self.cdb.dealloc(cls);
            } else {
                i += 1;
            }
        }
    }

    fn remove_rels(&mut self, rels: Vec<usize>) {
        let relset = GHashSet::from_iter(rels.iter().copied());
        let outs = GHashSet::from_iter(rels.iter().map(|&cls| self.cdb[cls].last()));
        for o in outs {
            let mut i = 0;
            while i < self.cnf[o].len() {
                if relset.contains(&self.cnf[o][i]) {
                    let cls = self.cnf[o].swap_remove(i);
                    if let Some((occur, qbve)) = &mut self.occur {
                        for &l in self.cdb[cls].iter() {
                            let lv = l.var();
                            if lv != o.var() {
                                occur.del(l, cls);
                                qbve.up(lv);
                            }
                        }
                    }
                    self.cdb.dealloc(cls);
                } else {
                    i += 1;
                }
            }
        }
    }

    #[inline]
    fn remove_node(&mut self, n: Var) {
        let ln = n.lit();
        if let Some((occur, _)) = &mut self.occur {
            assert!(occur.num_occur(ln) == 0 && occur.num_occur(!ln) == 0);
        }
        for &cls in self.cnf[ln].iter().chain(self.cnf[!ln].iter()) {
            if let Some((occur, qbve)) = &mut self.occur {
                for &l in self.cdb[cls].iter() {
                    let lv = l.var();
                    if lv != n {
                        occur.del(l, cls);
                        qbve.up(lv);
                    }
                }
            }
            self.cdb.dealloc(cls);
        }
        self.cnf[ln].clear();
        self.cnf[!ln].clear();
    }

    fn var_rels(&self, v: Var) -> Vec<usize> {
        self.cnf[v.lit()]
            .iter()
            .chain(self.cnf[!v.lit()].iter())
            .copied()
            .collect()
    }

    fn resolvent(
        &self,
        pcnf: &[usize],
        ncnf: &[usize],
        pivot: Var,
        limit: usize,
    ) -> Option<LitVvec> {
        let mut res = LitVvec::new();
        for &pcls in pcnf {
            for &ncls in ncnf {
                if let Some(resolvent) = self.cdb[pcls].ordered_resolvent(&self.cdb[ncls], pivot) {
                    res.push(resolvent);
                }
                if res.len() > limit {
                    return None;
                }
            }
        }
        Some(res)
    }

    fn eliminate(&mut self, v: Var) {
        if self.frozen.contains(&v) {
            return;
        }
        let lv = v.lit();
        let occur = &mut self.occur.as_mut().unwrap().0;
        let ocost =
            occur.num_occur(lv) + occur.num_occur(!lv) + self.cnf[lv].len() + self.cnf[!lv].len();
        if ocost == 0 || ocost > 2000 {
            return;
        }
        let (pos, neg) = (self.cnf[lv].clone(), self.cnf[!lv].clone());
        let mut ncost = 0;
        let mut opos = occur.get(lv).to_vec();
        let oneg = occur.get(!lv).to_vec();
        let Some(respn) = self.resolvent(&pos, &oneg, v, ocost - ncost) else {
            return;
        };
        ncost += respn.len();
        if ncost > ocost {
            return;
        }
        let Some(resnp) = self.resolvent(&neg, &opos, v, ocost - ncost) else {
            return;
        };
        ncost += resnp.len();
        if ncost > ocost {
            return;
        }
        let mut res = respn;
        res.extend(resnp);
        let res = clause_subsume_simplify(res);
        opos.extend(oneg);
        self.remove_rels(opos);
        self.remove_node(v);
        for r in res {
            self.add_rel(r);
        }
    }

    pub fn bve_simplify(&mut self) {
        let start = Instant::now();
        self.enable_occur();
        while let Some(v) = self.occur.as_mut().unwrap().1.pop() {
            self.eliminate(v);
        }
        self.time += start.elapsed();
    }

    fn cls_subsume_check(&mut self, ci: usize) {
        if self.cdb.is_removed(ci) {
            return;
        }
        let occur = &mut self.occur.as_mut().unwrap().0;
        let best_lit = *self.cdb[ci]
            .iter()
            .min_by_key(|&&l| {
                occur.num_occur(l) + occur.num_occur(!l) + self.cnf[l].len() + self.cnf[!l].len()
            })
            .unwrap();
        let mut occurs = occur.get(best_lit).to_vec();
        occurs.extend_from_slice(occur.get(!best_lit));
        occurs.extend(self.cnf[best_lit].iter());
        occurs.extend(self.cnf[!best_lit].iter());
        for cj in occurs {
            if self.cdb.is_removed(cj) {
                continue;
            }
            if cj == ci {
                continue;
            }
            let (res, diff) = self.cdb[ci].subsume_execpt_one(&self.cdb[cj]);
            if res {
                self.cnf[self.cdb[cj].last()].retain(|&c| c != cj);
                self.cdb.dealloc(cj);
                continue;
            } else if let Some(diff) = diff {
                if self.cdb[ci].len() == self.cdb[cj].len() {
                    if diff.var() == self.cdb[ci].last().var() {
                        self.cdb.dealloc(ci);
                        self.cdb.dealloc(cj);
                        self.cnf[self.cdb[ci].last()].retain(|&c| c != ci);
                        self.cnf[self.cdb[cj].last()].retain(|&c| c != cj);
                        return;
                    }
                    let mut cube = self.cdb[ci].cube().clone();
                    cube.retain(|l| *l != diff);
                    self.cdb[ci] = LitOrdVec::new(cube);
                    self.cnf[self.cdb[cj].last()].retain(|&c| c != cj);
                    self.cdb.dealloc(cj);
                } else if diff.var() == self.cdb[cj].last().var() {
                    self.cnf[self.cdb[cj].last()].retain(|&c| c != cj);
                    self.cdb.dealloc(cj);
                } else {
                    let mut cube = self.cdb[cj].cube().clone();
                    assert!(cube.last() == self.cdb[cj].last());
                    cube.retain(|l| *l != !diff);
                    self.cdb[cj] = LitOrdVec::new(cube);
                }
            }
        }
    }

    pub fn subsume_simplify(&mut self) {
        let start = Instant::now();
        self.enable_occur();
        for v in Var::CONST..=self.max_var {
            for cls in self.cnf[v.lit()].clone() {
                self.cls_subsume_check(cls);
            }
            for cls in self.cnf[!v.lit()].clone() {
                self.cls_subsume_check(cls);
            }
        }
        self.disable_occur();
        for v in Var::CONST..=self.max_var {
            self.cnf[v.lit()].retain(|&c| !self.cdb.is_removed(c));
            self.cnf[!v.lit()].retain(|&c| !self.cdb.is_removed(c));
        }
        self.time += start.elapsed();
    }

    fn const_simp_var(&mut self, v: Var) {
        let cls = self.var_rels(v);
        let mut removed = Vec::new();
        for c in cls {
            let cls = self.cdb[c].clone();
            if let Some(scls) = cls.ordered_simp(&self.value) {
                if scls.last().var() != v {
                    removed.push(c);
                } else if cls.len() != scls.len() {
                    self.add_rel(scls);
                }
            } else {
                removed.push(c);
            }
        }
        self.remove_rels(removed);
    }

    pub fn const_simplify(&mut self) {
        let start = Instant::now();
        self.disable_occur();
        for v in Var(1)..=self.max_var {
            self.const_simp_var(v);
        }
        for v in Var(1)..=self.max_var {
            let ln = v.lit();
            let vv = self.value.v(ln);
            if !vv.is_none() {
                self.remove_node(v);
                if self.frozen.contains(&v) {
                    self.add_rel(LitVec::from(ln.not_if(vv.is_false())));
                }
            }
        }
        self.time += start.elapsed();
    }

    pub fn finalize(&mut self) -> DagCnf {
        let start = Instant::now();
        let mut dagcnf = DagCnf::new();
        dagcnf.new_var_to(self.max_var);
        for v in Var(1)..=self.max_var {
            let mut cnf: Vec<_> = self.cnf[v.lit()]
                .iter()
                .chain(self.cnf[!v.lit()].iter())
                .map(|&cls| {
                    assert!(!self.cdb.is_removed(cls));
                    self.cdb[cls].cube().clone()
                })
                .collect();
            if self.frozen.contains(&v)
                && let Some(vl) = self.value.vl(v)
            {
                cnf.clear();
                cnf.push(LitVec::from(vl));
            }
            dagcnf.add_rel(v, &cnf);
        }
        self.time += start.elapsed();
        info!(
            "dagcnf simplified from {} to {} clauses in {:.2}s",
            self.num_ocls,
            dagcnf.num_clause(),
            self.time.as_secs_f64()
        );
        dagcnf
    }

    pub fn simplify(&mut self) -> DagCnf {
        self.const_simplify();
        self.bve_simplify();
        self.subsume_simplify();
        self.finalize()
    }
}

fn clause_subsume_simplify(lemmas: LitVvec) -> LitVvec {
    let lemmas: Vec<LitOrdVec> = lemmas.into_iter().map(LitOrdVec::new).collect();
    let lemmas = lemmas_subsume_simplify(lemmas);
    lemmas
        .into_iter()
        .map(|l| LitVec::from(l.cube().as_slice()))
        .collect()
}

impl DagCnf {
    pub fn simplify(&self, frozen: impl Iterator<Item = Var>) -> Self {
        let mut simp = DagCnfSimplify::new(self);
        for v in frozen.chain(once(Var::CONST)) {
            simp.froze(v);
        }
        simp.simplify()
    }
}

#[cfg(test)]
mod test {
    use crate::{DagCnf, Lit, Var, simplify::DagCnfSimplify};

    #[test]
    fn test0() {
        let mut dc = DagCnf::new();
        dc.new_var_to(Var(4));
        dc.new_and([Lit::from(1), Lit::from(2), Lit::from(3)]);
        dc.new_and([Lit::from(1), Lit::from(2), Lit::from(3), Lit::from(4)]);
        println!("{dc}");
        let mut simp = DagCnfSimplify::new(&dc);
        for v in Var::CONST..=dc.max_var() {
            simp.froze(v);
        }
        let ndc = simp.simplify();
        println!("{ndc}");
    }
}
