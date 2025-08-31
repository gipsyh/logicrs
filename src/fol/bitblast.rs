use super::{BvConst, Sort, Term, TermType, TermVec};
use crate::{DagCnf, Lit};
use giputils::hash::GHashMap;
use std::{iter::repeat_with, ops::Deref};

impl BvConst {
    #[inline]
    pub fn bitblast(&self) -> TermVec {
        self.iter().map(|c| Term::bool_const(*c)).collect()
    }

    #[inline]
    pub fn cnf_encode(&self) -> Lit {
        debug_assert!(self.len() == 1);
        Lit::constant(self[0])
    }
}

pub fn var_bitblast(sort: Sort) -> TermVec {
    let size = sort.size();
    repeat_with(|| Term::new_var(Sort::bool()))
        .take(size)
        .collect()
}

impl Term {
    pub fn bitblast(&self, map: &mut GHashMap<Term, TermVec>) -> TermVec {
        if let Some(res) = map.get(self) {
            return res.clone();
        }
        let blast = match self.deref() {
            TermType::Const(const_term) => const_term.bitblast(),
            TermType::Var(_) => var_bitblast(self.sort()),
            TermType::Op(op_term) => {
                let terms: Vec<TermVec> = op_term.terms.iter().map(|s| s.bitblast(map)).collect();
                op_term.op.bitblast(&terms)
            }
        };
        map.insert(self.clone(), blast.clone());
        map.get(self).unwrap().clone()
    }

    pub fn cnf_encode(&self, dc: &mut DagCnf, map: &mut GHashMap<Term, Lit>) -> Lit {
        if let Some(res) = map.get(self) {
            return *res;
        }
        let blast = match self.deref() {
            TermType::Const(const_term) => const_term.cnf_encode(),
            TermType::Var(_) => dc.new_var().lit(),
            TermType::Op(op_term) => {
                let terms: Vec<Lit> = op_term
                    .terms
                    .iter()
                    .map(|s| s.cnf_encode(dc, map))
                    .collect();
                op_term.op.cnf_encode(dc, &terms)
            }
        };
        map.insert(self.clone(), blast);
        *map.get(self).unwrap()
    }
}

pub fn bitblast_terms<'a, I: IntoIterator<Item = &'a Term>>(
    terms: I,
    map: &mut GHashMap<Term, TermVec>,
) -> impl Iterator<Item = TermVec> {
    terms.into_iter().map(|t| t.bitblast(map))
}

pub fn cnf_encode_terms<'a, I: IntoIterator<Item = &'a Term>>(
    terms: I,
    dc: &mut DagCnf,
    map: &mut GHashMap<Term, Lit>,
) -> impl Iterator<Item = Lit> {
    terms.into_iter().map(|t| t.cnf_encode(dc, map))
}
