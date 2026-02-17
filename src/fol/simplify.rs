use super::Term;
use super::op::{OptLevel, SimplifyCtx};
use crate::fol::OpTerm;
use crate::fol::op::OpTrait;
use giputils::hash::GHashMap;

impl OpTerm {
    fn op_simplify(&self, ctx: &SimplifyCtx, terms: &[Term]) -> Term {
        if let Some(res) = self.op.simplify(ctx, terms) {
            return res;
        }
        if self.op.traits().contains(OpTrait::Commutative) {
            debug_assert!(terms.len() == 2);
            let swapped = [terms[1].clone(), terms[0].clone()];
            if let Some(res) = self.op.simplify(ctx, &swapped) {
                return res;
            }
        }
        Term::new_op(self.op.clone(), terms)
    }
}

impl Term {
    pub fn simplify(&self, map: &mut GHashMap<Term, Term>) -> Term {
        self.simplify_with_ctx(&SimplifyCtx::default(), map)
    }

    pub fn simplify_with_ctx(&self, ctx: &SimplifyCtx, map: &mut GHashMap<Term, Term>) -> Term {
        if let Some(res) = map.get(self) {
            return res.clone();
        }
        let simp = match ctx.level {
            OptLevel::O0 => self.clone(),
            _ => {
                if let Some(op_term) = self.try_op() {
                    let terms: Vec<Term> = op_term
                        .terms
                        .iter()
                        .map(|s| s.simplify_with_ctx(ctx, map))
                        .collect();
                    op_term.op_simplify(ctx, &terms)
                } else {
                    self.clone()
                }
            }
        };
        map.insert(self.clone(), simp);
        map.get(self).unwrap().clone()
    }
}
