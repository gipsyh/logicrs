use super::Term;
use super::op::{OptLevel, SimplifyCtx};
use crate::fol::TermResult;
use crate::fol::op::{DynOp, OpTrait};
use giputils::hash::GHashMap;

fn op_simplify(ctx: &SimplifyCtx, op: DynOp, terms: &[Term]) -> TermResult {
    op.simplify(ctx, terms).or_else(|| {
        if op.traits().contains(OpTrait::Commutative) {
            debug_assert!(terms.len() == 2);
            op.simplify(ctx, &[terms[1].clone(), terms[0].clone()])
        } else {
            None
        }
    })
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
                    if let Some(res) = op_simplify(ctx, op_term.op.clone(), &terms) {
                        res.simplify_with_ctx(ctx, map)
                    } else {
                        Term::new_op(op_term.op.clone(), terms)
                    }
                } else {
                    self.clone()
                }
            }
        };
        map.insert(self.clone(), simp);
        map.get(self).unwrap().clone()
    }
}
