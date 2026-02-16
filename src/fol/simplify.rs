use super::Term;
use super::op::{OptLevel, SimplifyCtx};
use giputils::hash::GHashMap;

impl Term {
    pub fn simplify(&self, map: &mut GHashMap<Term, Term>) -> Term {
        self.simplify_with_ctx(&SimplifyCtx::default(), map)
    }

    pub fn simplify_with_level(&self, level: OptLevel, map: &mut GHashMap<Term, Term>) -> Term {
        self.simplify_with_ctx(&SimplifyCtx::new(level), map)
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
                    if let Some(new) = op_term.op.simplify(ctx, &terms) {
                        new
                    } else {
                        Term::new_op(op_term.op.clone(), &terms)
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
