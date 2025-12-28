use super::Term;
use giputils::hash::GHashMap;

impl Term {
    pub fn simplify(&self, map: &mut GHashMap<Term, Term>) -> Term {
        if let Some(res) = map.get(self) {
            return res.clone();
        }
        let simp = if let Some(op_term) = self.try_op() {
            let terms: Vec<Term> = op_term.terms.iter().map(|s| s.simplify(map)).collect();
            if let Some(new) = op_term.op.simplify(&terms) {
                new
            } else {
                Term::new_op(op_term.op.clone(), &terms)
            }
        } else {
            self.clone()
        };
        map.insert(self.clone(), simp);
        map.get(self).unwrap().clone()
    }
}
