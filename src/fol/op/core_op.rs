use super::super::bitblast::*;
use super::super::simplify::*;
use super::define::define_core_op;
use super::simulate::*;
use super::{OpTrait, Sort, Term};
use crate::fol::op::define::define_core_fold_op;
use crate::{DagCnf, Lit, LitVvec};

#[inline]
fn bool_sort(_terms: &[Term]) -> Sort {
    Sort::Bv(1)
}

define_core_op!(Not, 1, traits: OpTrait::Involutive.into(), bitblast: not_bitblast, cnf_encode: not_cnf_encode, simulate: not_simulate);
fn not_cnf_encode(_dc: &mut DagCnf, terms: &[Lit]) -> Lit {
    !terms[0]
}

define_core_op!(And, 2, traits: OpTrait::Commutative | OpTrait::Associative | OpTrait::Idempotent, bitblast: and_bitblast, cnf_encode: and_cnf_encode, simplify: and_simplify, simulate: and_simulate);
fn and_cnf_encode(dc: &mut DagCnf, terms: &[Lit]) -> Lit {
    let l = dc.new_var().lit();
    dc.add_rel(l.var(), &LitVvec::cnf_and(l, terms));
    l
}

define_core_fold_op!(Ands, cnf_encode: ands_cnf_encode, simulate: ands_simulate);
fn ands_cnf_encode(dc: &mut DagCnf, terms: &[Lit]) -> Lit {
    let l = dc.new_var().lit();
    dc.add_rel(l.var(), &LitVvec::cnf_and(l, terms));
    l
}

define_core_op!(Or, 2, traits: OpTrait::Commutative | OpTrait::Associative | OpTrait::Idempotent, bitblast: or_bitblast, cnf_encode: or_cnf_encode, simplify: or_simplify, simulate: or_simulate);
fn or_cnf_encode(dc: &mut DagCnf, terms: &[Lit]) -> Lit {
    let l = dc.new_var().lit();
    dc.add_rel(l.var(), &LitVvec::cnf_or(l, terms));
    l
}

define_core_fold_op!(Ors, cnf_encode: ors_cnf_encode, simulate: ors_simulate);
fn ors_cnf_encode(dc: &mut DagCnf, terms: &[Lit]) -> Lit {
    let l = dc.new_var().lit();
    dc.add_rel(l.var(), &LitVvec::cnf_or(l, terms));
    l
}

define_core_op!(Xor, 2, traits: OpTrait::Commutative | OpTrait::Associative, bitblast: xor_bitblast, cnf_encode: xor_cnf_encode, simplify: xor_simplify, simulate: xor_simulate);
fn xor_cnf_encode(dc: &mut DagCnf, terms: &[Lit]) -> Lit {
    let l = dc.new_var().lit();
    dc.add_rel(l.var(), &LitVvec::cnf_xor(l, terms[0], terms[1]));
    l
}

define_core_op!(Eq, 2, traits: OpTrait::Commutative.into(), sort: bool_sort, bitblast: eq_bitblast, cnf_encode: eq_cnf_encode, simplify: eq_simplify, simulate: eq_simulate);
fn eq_cnf_encode(dc: &mut DagCnf, terms: &[Lit]) -> Lit {
    let l = dc.new_var().lit();
    dc.add_rel(l.var(), &LitVvec::cnf_xnor(l, terms[0], terms[1]));
    l
}

define_core_op!(Ult, 2, sort: bool_sort, bitblast: ult_bitblast, simplify: ult_simplify, simulate: ult_simulate);

define_core_op!(Slt, 2, sort: bool_sort, bitblast: slt_bitblast, simulate: slt_simulate);

define_core_op!(Sll, 2, bitblast: sll_bitblast, simulate: sll_simulate);

define_core_op!(Srl, 2, bitblast: srl_bitblast, simulate: srl_simulate);

define_core_op!(Sra, 2, bitblast: sra_bitblast, simulate: sra_simulate);

define_core_op!(Rol, 2, bitblast: rol_bitblast, simulate: rol_simulate);

define_core_op!(Ror, 2, bitblast: ror_bitblast, simulate: ror_simulate);

define_core_op!(Ite, 3, sort: ite_sort, bitblast: ite_bitblast, cnf_encode: ite_cnf_encode, simplify: ite_simplify, simulate: ite_simulate);
fn ite_sort(terms: &[Term]) -> Sort {
    terms[1].sort()
}
fn ite_cnf_encode(dc: &mut DagCnf, terms: &[Lit]) -> Lit {
    let l = dc.new_var().lit();
    dc.add_rel(l.var(), &LitVvec::cnf_ite(l, terms[0], terms[1], terms[2]));
    l
}

define_core_op!(Concat, 2, sort: concat_sort, bitblast: concat_bitblast, simplify: concat_simplify, simulate: concat_simulate);
fn concat_sort(terms: &[Term]) -> Sort {
    Sort::Bv(terms[0].bv_len() + terms[1].bv_len())
}

define_core_op!(Sext, 2, sort: sext_sort, bitblast: sext_bitblast, simplify: sext_simplify, simulate: sext_simulate);
fn sext_sort(terms: &[Term]) -> Sort {
    Sort::Bv(terms[0].bv_len() + terms[1].bv_len())
}

define_core_op!(Slice, 3, sort: slice_sort, bitblast: slice_bitblast, simplify: slice_simplify, simulate: slice_simulate);
fn slice_sort(terms: &[Term]) -> Sort {
    Sort::Bv(terms[1].bv_len() - terms[2].bv_len() + 1)
}

define_core_op!(Redxor, 1, sort: bool_sort, bitblast: redxor_bitblast, simulate: redxor_simulate);

define_core_op!(Add, 2, traits: OpTrait::Commutative | OpTrait::Associative, bitblast: add_bitblast, simulate: add_simulate);

define_core_op!(Sub, 2, bitblast: sub_bitblast, simplify: sub_simplify, simulate: sub_simulate);

// define_core_op!(Uaddo, 2, sort: bool_sort, bitblast: uaddo_bitblast);
// fn uaddo_bitblast(terms: &[TermVec]) -> TermVec {
//     let mut x = terms[0].clone();
//     let mut y = terms[1].clone();
//     x.push(Term::bool_const(false));
//     y.push(Term::bool_const(false));
//     x = add_bitblast(&[x, y]);
//     [x[x.len() - 1].clone()].into()
// }
// define_core_op!(Saddo, 2, sort: bool_sort, bitblast: saddo_bitblast);
// fn saddo_bitblast(terms: &[TermVec]) -> TermVec {
//     assert_eq!(terms.len(), 2);
//     let w = terms[0].len();
//     let sx = &terms[0][w - 1]; // sign bits
//     let sy = &terms[1][w - 1];
//     let sum = add_bitblast(terms);
//     let ss = &sum[w - 1];
//     let v1 = sx & sy & !ss;
//     let v2 = !sx & !sy & ss;
//     TermVec::from([v1 | v2])
// }
// define_core_op!(Ssubo, 2, sort: bool_sort, bitblast: ssubo_bitblast);
// fn ssubo_bitblast(terms: &[TermVec]) -> TermVec {
//     assert_eq!(terms.len(), 2);
//     let w = terms[0].len();
//     let sx = &terms[0][w - 1];
//     let sy = &terms[1][w - 1];
//     // compute w-bit (x - y) discarding carry_out
//     let diff = sub_bitblast(terms);
//     let sr = &diff[w - 1];
//     let v1 = sx & !sy & !sr;
//     let v2 = !sx & sy & sr;
//     TermVec::from([v1 | v2])
// }

// define_core_op!(Umulo, 2, sort: bool_sort, bitblast: umulo_bitblast);

// define_core_op!(Smulo, 2, sort: bool_sort, bitblast: smulo_bitblast);

define_core_op!(Mul, 2, traits: OpTrait::Commutative | OpTrait::Associative, bitblast: mul_bitblast, simplify: mul_simplify, simulate: mul_simulate);

define_core_op!(Udiv, 2, bitblast: udiv_bitblast, simplify: udiv_simplify, simulate: udiv_simulate);

define_core_op!(Urem, 2, bitblast: urem_bitblast, simulate: urem_simulate);

define_core_op!(Neg, 1, traits: OpTrait::Involutive.into(), bitblast: neg_bitblast, simulate: neg_simulate);

define_core_op!(Sdiv, 2, bitblast: sdiv_bitblast, simulate: sdiv_simulate);

define_core_op!(Srem, 2, bitblast: srem_bitblast, simulate: srem_simulate);

define_core_op!(Smod, 2, bitblast: smod_bitblast, simulate: smod_simulate);

// define_core_op!(Sdivo, 2, sort: bool_sort, bitblast: sdivo_bitblast);
// ...

define_core_op!(Read, 2, sort: read_sort, bitblast: read_bitblast, simulate: read_simulate);
fn read_sort(terms: &[Term]) -> Sort {
    let (_, e) = terms[0].sort().array();
    Sort::Bv(e)
}

define_core_op!(Write, 3, bitblast: write_bitblast, simulate: write_simulate);
