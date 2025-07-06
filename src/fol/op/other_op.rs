use super::Term;
use super::define::define_non_core_op;
use super::{Concat, Eq, Slt, Ult, Xor};

define_non_core_op!(Neg, 1, neg_normalize);
fn neg_normalize(terms: &[Term]) -> Term {
    let term = &terms[0];
    !term + term.mk_bv_const_one()
}

define_non_core_op!(Inc, 1, inc_normalize);
fn inc_normalize(terms: &[Term]) -> Term {
    &terms[0] + terms[0].mk_bv_const_one()
}

define_non_core_op!(Dec, 1, dec_normalize);
fn dec_normalize(terms: &[Term]) -> Term {
    &terms[0] - terms[0].mk_bv_const_one()
}

define_non_core_op!(Nand, 2, nand_normalize);
fn nand_normalize(terms: &[Term]) -> Term {
    !(&terms[0] & &terms[1])
}
define_non_core_op!(Nor, 2, nor_normalize);
fn nor_normalize(terms: &[Term]) -> Term {
    !(&terms[0] | &terms[1])
}
define_non_core_op!(Xnor, 2, xnor_normalize);
fn xnor_normalize(terms: &[Term]) -> Term {
    !Term::new_op(Xor, terms)
}

define_non_core_op!(Iff, 2, iff_normalize);
fn iff_normalize(terms: &[Term]) -> Term {
    terms[0].op1(Eq, &terms[1])
}
define_non_core_op!(Implies, 2, implies_normalize);
fn implies_normalize(terms: &[Term]) -> Term {
    !&terms[0] | &terms[1]
}

// redand: x = 111111111
define_non_core_op!(Redand, 1, redand_normalize);
fn redand_normalize(terms: &[Term]) -> Term {
    let ones = terms[0].mk_bv_const_ones();
    terms[0].op1(Eq, &ones)
}
// redor: x != 00000000
define_non_core_op!(Redor, 1, redor_normalize);
fn redor_normalize(terms: &[Term]) -> Term {
    let zero = terms[0].mk_bv_const_zero();
    !terms[0].op1(Eq, &zero)
}
// udivo: y != 00000000
define_non_core_op!(Udivo, 2, udivo_normalize);
fn udivo_normalize(terms: &[Term]) -> Term {
    let zero = terms[1].mk_bv_const_zero();
    !terms[1].op1(Eq, &zero)
}
define_non_core_op!(Neq, 2, neq_normalize);
fn neq_normalize(terms: &[Term]) -> Term {
    !Term::new_op(Eq, terms)
}

define_non_core_op!(Uext, 2, uext_normalize);
fn uext_normalize(terms: &[Term]) -> Term {
    if terms[1].bv_len() == 0 {
        terms[0].clone()
    } else {
        Term::new_op(Concat, &[terms[1].clone(), terms[0].clone()])
    }
}

define_non_core_op!(Ugt, 2, ugt_normalize);
fn ugt_normalize(terms: &[Term]) -> Term {
    terms[1].op1(Ult, &terms[0])
}

define_non_core_op!(Ulte, 2, ulte_normalize);
fn ulte_normalize(terms: &[Term]) -> Term {
    !terms[1].op1(Ult, &terms[0])
}

define_non_core_op!(Ugte, 2, ugte_normalize);
fn ugte_normalize(terms: &[Term]) -> Term {
    !Term::new_op(Ult, terms)
}

define_non_core_op!(Sgt, 2, sgt_normalize);
fn sgt_normalize(terms: &[Term]) -> Term {
    terms[1].op1(Slt, &terms[0])
}

define_non_core_op!(Slte, 2, slte_normalize);
fn slte_normalize(terms: &[Term]) -> Term {
    !terms[1].op1(Slt, &terms[0])
}

define_non_core_op!(Sgte, 2, sgte_normalize);
fn sgte_normalize(terms: &[Term]) -> Term {
    !Term::new_op(Slt, terms)
}
