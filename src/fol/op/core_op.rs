use super::define::define_core_op;
use super::simulate::*;
use super::{Sort, Term, TermResult, TermVec};
use crate::fol::op::define::define_core_fold_op;
use crate::{DagCnf, Lit, LitVvec};
use std::slice;

#[inline]
fn bool_sort(_terms: &[Term]) -> Sort {
    Sort::Bv(1)
}

define_core_op!(Not, 1, bitblast: not_bitblast, cnf_encode: not_cnf_encode, simplify: not_simplify, simulate: not_simulate);
fn not_simplify(terms: &[Term]) -> TermResult {
    let x = &terms[0];
    if let Some(op) = x.try_op()
        && op.op == Not
    {
        return Some(op[0].clone());
    }
    if let Some(xc) = x.try_bv_const() {
        return Some(Term::bv_const(!xc));
    }
    None
}
fn not_bitblast(terms: &[TermVec]) -> TermVec {
    terms[0].iter().map(|t| !t).collect()
}
fn not_cnf_encode(_dc: &mut DagCnf, terms: &[Lit]) -> Lit {
    !terms[0]
}

define_core_op!(And, 2, bitblast: and_bitblast, cnf_encode: and_cnf_encode, simplify: and_simplify, simulate: and_simulate);

fn ordered_and_simplify(a: &Term, b: &Term) -> TermResult {
    if let Some(ac) = a.try_bv_const() {
        if ac.is_ones() {
            return Some(b.clone());
        }
        if ac.is_zero() {
            return Some(a.clone());
        }
    }
    if a == b {
        return Some(a.clone());
    }
    if a == !b {
        return Some(a.mk_bv_const_zero());
    }
    if let Some(aop) = a.try_op() {
        if aop.op == And {
            if let Some(bop) = b.try_op()
                && bop.op == And
            {
                if aop[0] == bop[0] {
                    return Some(&aop[0] & &aop[1] & &bop[1]);
                }
                if aop[0] == bop[1] {
                    return Some(&aop[0] & &aop[1] & &bop[0]);
                }
            }
            if b == aop[0] {
                return Some(b & &aop[1]);
            }
            if b == aop[1] {
                return Some(b & &aop[0]);
            }
        }
        if aop.op == Not
            && let Some(bop) = b.try_op()
            && bop.op == Not
        {
            return Some(!(&aop[0] | &bop[0]));
        }
        if aop.op == Or {
            if aop[0] == b || aop[1] == b {
                return Some(b.clone());
            }
            if let Some(bop) = b.try_op()
                && bop.op == Or
            {
                if aop[0] == bop[0] {
                    return Some(&aop[0] | (&aop[1] & &bop[1]));
                }
                if aop[0] == bop[1] {
                    return Some(&aop[0] | (&aop[1] & &bop[0]));
                }
            }
        }
    }
    None
}
fn and_simplify(terms: &[Term]) -> TermResult {
    let x = &terms[0];
    let y = &terms[1];
    ordered_and_simplify(x, y)?;
    ordered_and_simplify(y, x)
}
fn and_bitblast(terms: &[TermVec]) -> TermVec {
    Term::new_op_elementwise(And, &terms[0], &terms[1])
}
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

define_core_op!(Or, 2, bitblast: or_bitblast, cnf_encode: or_cnf_encode, simplify: or_simplify, simulate: or_simulate);
fn or_simplify(terms: &[Term]) -> TermResult {
    let x = &terms[0];
    let y = &terms[1];
    let simp = |a: &Term, b: &Term| {
        if let Some(ac) = a.try_bv_const() {
            if ac.is_ones() {
                return Some(a.clone());
            }
            if ac.is_zero() {
                return Some(b.clone());
            }
        }
        if a == b {
            return Some(a.clone());
        }
        if a == !b {
            return Some(a.mk_bv_const_ones());
        }
        if let Some(aop) = a.try_op() {
            if aop.op == Or {
                if b == aop[0] {
                    return Some(b | &aop[1]);
                }
                if b == aop[1] {
                    return Some(b | &aop[0]);
                }
            }
            if aop.op == Not
                && let Some(bop) = b.try_op()
                && bop.op == Not
            {
                return Some(!(&aop[0] & &bop[0]));
            }
            if aop.op == Ite {
                if b == aop[0] {
                    return Some(b | &aop[2]);
                }
                if b == !&aop[0] {
                    return Some(b | &aop[1]);
                }
            }
            if aop.op == And
                && let Some(bop) = b.try_op()
                && bop.op == And
            {
                if aop[0] == bop[0] {
                    return Some(&aop[0] & (&aop[1] | &bop[1]));
                }
                if aop[0] == bop[1] {
                    return Some(&aop[0] & (&aop[1] | &bop[0]));
                }
            }
        }
        None
    };
    simp(x, y)?;
    simp(y, x)
}
fn or_bitblast(terms: &[TermVec]) -> TermVec {
    Term::new_op_elementwise(Or, &terms[0], &terms[1])
}
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

define_core_op!(Xor, 2, bitblast: xor_bitblast, cnf_encode: xor_cnf_encode, simplify: xor_simplify, simulate: xor_simulate);
fn xor_simplify(terms: &[Term]) -> TermResult {
    let x = &terms[0];
    let y = &terms[1];
    let simp = |a: &Term, b: &Term| {
        if let Some(ac) = a.try_bv_const() {
            if ac.is_ones() {
                return Some(!b.clone());
            }
            if ac.is_zero() {
                return Some(b.clone());
            }
        }
        if a == b {
            return Some(a.mk_bv_const_zero());
        }
        if a == !b {
            return Some(a.mk_bv_const_ones());
        }
        None
    };
    simp(x, y)?;
    simp(y, x)
}
fn xor_bitblast(terms: &[TermVec]) -> TermVec {
    Term::new_op_elementwise(Xor, &terms[0], &terms[1])
}
fn xor_cnf_encode(dc: &mut DagCnf, terms: &[Lit]) -> Lit {
    let l = dc.new_var().lit();
    dc.add_rel(l.var(), &LitVvec::cnf_xor(l, terms[0], terms[1]));
    l
}

define_core_op!(Eq, 2, sort: bool_sort, bitblast: eq_bitblast, cnf_encode: eq_cnf_encode, simplify: eq_simplify, simulate: eq_simulate);
fn eq_simplify(terms: &[Term]) -> TermResult {
    let x = &terms[0];
    let y = &terms[1];
    let simp = |a: &Term, b: &Term| {
        if a.is_bool()
            && let Some(s) = xor_simplify(terms)
        {
            return Some(!s);
        }
        if a == b {
            return Some(Term::bool_const(true));
        }
        if a == !b {
            return Some(Term::bool_const(false));
        }
        None
    };
    simp(x, y)?;
    simp(y, x)
}
fn eq_bitblast(terms: &[TermVec]) -> TermVec {
    let neqs = Term::new_op_elementwise(Eq, &terms[0], &terms[1]);
    TermVec::from([Term::new_op(Ands, &neqs)])
}
fn eq_cnf_encode(dc: &mut DagCnf, terms: &[Lit]) -> Lit {
    let l = dc.new_var().lit();
    dc.add_rel(l.var(), &LitVvec::cnf_xnor(l, terms[0], terms[1]));
    l
}

define_core_op!(Ult, 2, sort: bool_sort, bitblast: ult_bitblast, simplify: ult_simplify, simulate: ult_simulate);
// define_core_op!(Usubo, 2, sort: bool_sort, bitblast: ult_bitblast, simplify: ult_simplify);
fn ult_simplify(terms: &[Term]) -> TermResult {
    let x = &terms[0];
    let y = &terms[1];
    if let Some(xc) = x.try_bv_const() {
        if xc.is_zero() {
            return Some(!x.op1(Eq, y));
        }
        if xc.is_ones() {
            return Some(Term::bool_const(false));
        }
    }
    if let Some(yc) = y.try_bv_const() {
        if yc.is_zero() {
            return Some(Term::bool_const(false));
        }
        if yc.is_ones() {
            return Some(!x.op1(Eq, y));
        }
    }
    None
}
fn ult_bitblast(terms: &[TermVec]) -> TermVec {
    let mut res = Term::bool_const(false);
    for (x, y) in terms[0].iter().zip(terms[1].iter()) {
        res = (!x & y) | ((!x | y) & res)
    }
    TermVec::from([res])
}

define_core_op!(Slt, 2, sort: bool_sort, bitblast: slt_bitblast, simulate: slt_simulate);
fn slt_bitblast(terms: &[TermVec]) -> TermVec {
    let x = &terms[0];
    let y = &terms[1];
    let len = x.len();
    let (xr, xs) = (&x[..len - 1], &x[len - 1]);
    let (yr, ys) = (&y[..len - 1], &y[len - 1]);
    let ls = xs & !ys;
    let eqs = xs.op1(Eq, ys);
    let mut el = Term::bool_const(false);
    for (x, y) in xr.iter().zip(yr.iter()) {
        el = (!x & y) | ((!x | y) & el)
    }
    TermVec::from([ls | (eqs & el)])
}

define_core_op!(Sll, 2, bitblast: sll_bitblast, simulate: sll_simulate);
fn sll_bitblast(terms: &[TermVec]) -> TermVec {
    let (x, y) = (&terms[0], &terms[1]);
    assert!(x.len() == y.len());
    if terms[0].len() == 1 {
        return TermVec::from([&x[0] & !&y[0]]);
    }
    let width = x.len();
    // ceil(log2(width))
    let stages = (usize::BITS - (width - 1).leading_zeros()) as usize;
    let mut res = x.clone();
    for shift_bit in 0..stages {
        let shift_step = 1 << shift_bit;
        let shift = &y[shift_bit];
        let mut nres = TermVec::new();
        for j in 0..shift_step.min(width) {
            nres.push(&!shift & &res[j]);
        }
        for j in shift_step..width {
            nres.push(Term::new_op(Ite, [shift, &res[j - shift_step], &res[j]]));
        }
        res = nres;
    }

    if stages < width {
        let no_toobig = !Term::new_op(Ors, &y[stages..]);
        res = res
            .into_iter()
            .map(|b| Term::new_op(And, [&no_toobig, &b]))
            .collect();
    }
    res
}

define_core_op!(Srl, 2, bitblast: srl_bitblast, simulate: srl_simulate);
fn srl_bitblast(terms: &[TermVec]) -> TermVec {
    let (x, y) = (&terms[0], &terms[1]);
    assert!(x.len() == y.len());
    if terms[0].len() == 1 {
        return TermVec::from([&x[0] & !&y[0]]);
    }
    let width = x.len();
    let stages = (usize::BITS - (width - 1).leading_zeros()) as usize;
    let mut res = x.clone();
    for shift_bit in 0..stages {
        let shift_step = 1 << shift_bit;
        let shift = &y[shift_bit];
        let mut nres = TermVec::new();
        let c = width.saturating_sub(shift_step);
        for j in 0..c {
            nres.push(Term::new_op(Ite, [shift, &res[j + shift_step], &res[j]]));
        }
        for j in c..width {
            nres.push(&!shift & &res[j]);
        }
        res = nres;
    }

    if stages < width {
        let not_toobig = !Term::new_op(Ors, &y[stages..]);
        res = res
            .into_iter()
            .map(|b| Term::new_op(And, [&not_toobig, &b]))
            .collect();
    }
    res
}

define_core_op!(Sra, 2, bitblast: sra_bitblast, simulate: sra_simulate);
fn sra_bitblast(terms: &[TermVec]) -> TermVec {
    let (x, y) = (&terms[0], &terms[1]);
    assert!(x.len() == y.len());
    if terms[0].len() == 1 {
        return x.clone();
    }
    let width = x.len();
    let stages = (usize::BITS - (width - 1).leading_zeros()) as usize;
    let mut res = x.clone();
    for shift_bit in 0..stages {
        let shift_step = 1 << shift_bit;
        let c = width.saturating_sub(shift_step);
        let shift = &y[shift_bit];
        let mut nres = TermVec::new();
        for j in 0..c {
            nres.push(Term::new_op(Ite, [shift, &res[j + shift_step], &res[j]]));
        }
        for j in c..width {
            nres.push(Term::new_op(Ite, [shift, &res[width - 1], &res[j]]));
        }
        res = nres;
    }

    if stages < width {
        let not_toobig = !Term::new_op(Ors, &y[stages..]);
        let sign = res[width - 1].clone();
        res = res
            .into_iter()
            .map(|b| Term::new_op(Ite, [&not_toobig, &b, &sign]))
            .collect();
    }
    res
}

define_core_op!(Rol, 2, bitblast: rol_bitblast, simulate: rol_simulate);
fn rol_bitblast(terms: &[TermVec]) -> TermVec {
    let (x, y) = (&terms[0], &terms[1]);
    assert_eq!(x.len(), y.len());
    let width = x.len();
    // width = 1: rotation is a no-op
    if width == 1 {
        return x.clone();
    }
    let stages = match width & (width - 1) {
        // power of 2 ?
        0 => (usize::BITS - (width - 1).leading_zeros()) as usize,
        _ => width,
    };
    assert!(stages < usize::BITS as usize);

    let mut res = x.clone();
    for shift_bit in 0..stages {
        let shift_step = 1 << shift_bit;
        let shift = &y[shift_bit];
        let mut next = TermVec::new();
        for j in 0..width {
            // wrap-around index for rotate-left
            let src = (j + width - shift_step % width) % width;
            if src == j {
                next.push(res[j].clone());
            } else {
                next.push(Term::new_op(Ite, [shift, &res[src], &res[j]]));
            }
        }
        res = next;
    }
    res
}

define_core_op!(Ror, 2, bitblast: ror_bitblast, simulate: ror_simulate);
fn ror_bitblast(terms: &[TermVec]) -> TermVec {
    let (x, y) = (&terms[0], &terms[1]);
    assert_eq!(x.len(), y.len());
    let width = x.len();
    if width == 1 {
        return x.clone();
    }
    let stages = match width & (width - 1) {
        // power of 2 ?
        0 => (usize::BITS - (width - 1).leading_zeros()) as usize,
        _ => width,
    };
    assert!(stages < usize::BITS as usize);

    let mut res = x.clone();
    for shift_bit in 0..stages {
        let shift_step = 1 << shift_bit;
        let shift = &y[shift_bit];
        let mut next = TermVec::new();
        for j in 0..width {
            let src = (j + shift_step) % width;
            if src == j {
                next.push(res[j].clone());
            } else {
                next.push(Term::new_op(Ite, [shift, &res[src], &res[j]]));
            }
        }
        res = next;
    }
    res
}

define_core_op!(Ite, 3, sort: ite_sort, bitblast: ite_bitblast, cnf_encode: ite_cnf_encode, simplify: ite_simplify, simulate: ite_simulate);
fn ite_sort(terms: &[Term]) -> Sort {
    terms[1].sort()
}
fn ite_simplify(terms: &[Term]) -> TermResult {
    let (c, t, e) = (&terms[0], &terms[1], &terms[2]);
    if let Some(cc) = c.try_bv_const() {
        if cc.is_ones() {
            return Some(t.clone());
        } else {
            return Some(e.clone());
        }
    }
    if t == e {
        return Some(t.clone());
    }
    if let Some(cop) = c.try_op()
        && cop.op == Not
    {
        return Some(cop[0].ite(e, t));
    }
    if t.is_bool() {
        if let Some(ec) = e.try_bv_const() {
            if ec.is_zero() {
                return Some(c & t);
            }
            if ec.is_ones() {
                return Some(!c | t);
            }
        }
        if let Some(tc) = t.try_bv_const() {
            if tc.is_zero() {
                return Some(!c & e);
            }
            if tc.is_ones() {
                return Some(c | e);
            }
        }
    }
    None
}
fn ite_bitblast(terms: &[TermVec]) -> TermVec {
    let mut res = TermVec::new();
    for (x, y) in terms[1].iter().zip(terms[2].iter()) {
        res.push(terms[0][0].op2(Ite, x, y));
    }
    res
}
fn ite_cnf_encode(dc: &mut DagCnf, terms: &[Lit]) -> Lit {
    let l = dc.new_var().lit();
    dc.add_rel(l.var(), &LitVvec::cnf_ite(l, terms[0], terms[1], terms[2]));
    l
}

define_core_op!(Concat, 2, sort: concat_sort, bitblast: concat_bitblast, simplify: concat_simplify, simulate: concat_simulate);
fn concat_simplify(terms: &[Term]) -> TermResult {
    let x = &terms[0];
    let y = &terms[1];
    if let (Some(xc), Some(yc)) = (x.try_bv_const(), y.try_bv_const()) {
        let mut c = yc.clone();
        c.extend(xc.iter());
        return Some(Term::bv_const(c));
    }
    None
}
fn concat_sort(terms: &[Term]) -> Sort {
    Sort::Bv(terms[0].bv_len() + terms[1].bv_len())
}
fn concat_bitblast(terms: &[TermVec]) -> TermVec {
    let mut res = terms[1].clone();
    res.extend_from_slice(&terms[0]);
    res
}

define_core_op!(Sext, 2, sort: sext_sort, bitblast: sext_bitblast, simulate: sext_simulate);
fn sext_sort(terms: &[Term]) -> Sort {
    Sort::Bv(terms[0].bv_len() + terms[1].bv_len())
}
fn sext_bitblast(terms: &[TermVec]) -> TermVec {
    let x = &terms[0];
    let mut res = x.clone();
    let ext = vec![x[x.len() - 1].clone(); terms[1].len()];
    res.extend(ext);
    res
}

define_core_op!(Slice, 3, sort: slice_sort, bitblast: slice_bitblast, simplify: slice_simplify, simulate: slice_simulate);
fn slice_sort(terms: &[Term]) -> Sort {
    Sort::Bv(terms[1].bv_len() - terms[2].bv_len() + 1)
}
fn slice_bitblast(terms: &[TermVec]) -> TermVec {
    let l = terms[2].len();
    let h = terms[1].len();
    terms[0][l..=h].iter().cloned().collect()
}
fn slice_simplify(terms: &[Term]) -> TermResult {
    let s = &terms[0];
    let l = terms[2].bv_len();
    let h = terms[1].bv_len();
    if l == 0 && h == 0 && s.bv_len() == 1 {
        return Some(s.clone());
    }
    None
}

define_core_op!(Redxor, 1, sort: bool_sort, bitblast: redxor_bitblast, simulate: redxor_simulate);
fn redxor_bitblast(terms: &[TermVec]) -> TermVec {
    TermVec::from([Term::new_op_fold(Xor, terms[0].iter())])
}

#[inline]
fn full_adder(x: &Term, y: &Term, c: &Term) -> (Term, Term) {
    let r = Term::new_op_fold(Xor, [x, y, c]);
    let xy = x & y;
    let xc = x & c;
    let yc = y & c;
    let c = Term::new_op(Ors, [&xy, &xc, &yc]);
    (r, c)
}

define_core_op!(Add, 2, bitblast: add_bitblast, simulate: add_simulate);
fn add_bitblast(terms: &[TermVec]) -> TermVec {
    let mut r;
    let mut c = Term::bool_const(false);
    let mut res = TermVec::new();
    for (x, y) in terms[0].iter().zip(terms[1].iter()) {
        (r, c) = full_adder(x, y, &c);
        res.push(r);
    }
    res
}
define_core_op!(Sub, 2, bitblast: sub_bitblast, simplify: sub_simplify, simulate: sub_simulate);
fn sub_bitblast(terms: &[TermVec]) -> TermVec {
    let mut r;
    let mut c = Term::bool_const(true);
    let mut res = TermVec::new();
    for (x, y) in terms[0].iter().zip(terms[1].iter()) {
        (r, c) = full_adder(x, &!y, &c);
        res.push(r);
    }
    res
}
fn sub_simplify(terms: &[Term]) -> TermResult {
    let (x, y) = (&terms[0], &terms[1]);
    if let Some(yc) = y.try_bv_const() {
        if yc.is_zero() {
            return Some(x.clone());
        }
        if x.bv_len() == 1 && yc.is_one() {
            return Some(!x.clone());
        }
    }
    None
}

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

define_core_op!(Mul, 2, bitblast: mul_bitblast, simplify: mul_simplify, simulate: mul_simulate);
fn mul_bitblast(terms: &[TermVec]) -> TermVec {
    let x = &terms[0];
    let y = &terms[1];
    assert!(x.len() == y.len());
    let len = x.len();
    let mut res: TermVec = x.iter().map(|t| t & &y[0]).collect();
    for i in 1..len {
        let mut c = Term::bool_const(false);
        for j in i..len {
            let add = &y[i] & &x[j - i];
            (res[j], c) = full_adder(&res[j], &add, &c);
        }
    }
    res
}

fn ordered_mul_simplify(x: &Term, y: &Term) -> TermResult {
    if let Some(xc) = x.try_bv_const() {
        if xc.is_zero() {
            return Some(x.clone());
        }
        if xc.is_one() {
            return Some(y.clone());
        }
    }
    None
}

fn mul_simplify(terms: &[Term]) -> TermResult {
    let (x, y) = (&terms[0], &terms[1]);
    ordered_mul_simplify(x, y)?;
    ordered_mul_simplify(y, x)
}

// define_core_op!(Umulo, 2, sort: bool_sort, bitblast: umulo_bitblast);
// fn umulo_bitblast(terms: &[TermVec]) -> TermVec {
//     /* Unsigned multiplication overflow detection.
//      * See M.Gok, M.J. Schulte, P.I. Balzola, "Efficient integer multiplication
//      * overflow detection circuits", 2001.
//      * http://ieeexplore.ieee.org/document/987767 */
//     let (mut x, mut y) = (terms[0].clone(), terms[1].clone());
//     let k = x.len();
//     if k == 1 {
//         return TermVec::from([Term::bool_const(false)]);
//     }
//     let mut uppc = x[k - 1].clone();
//     let mut res = Term::bool_const(false);
//     for i in 1..k {
//         let aand = &uppc & &y[i];
//         res = &res | &aand;
//         uppc = &x[k - 1 - i] | &uppc;
//     }
//     x.push(Term::bool_const(false));
//     y.push(Term::bool_const(false));
//     let mul = mul_bitblast(&[x, y]);
//     TermVec::from([&res | &mul[k]])
// }

// define_core_op!(Smulo, 2, sort: bool_sort, bitblast: smulo_bitblast);
// fn smulo_bitblast(terms: &[TermVec]) -> TermVec {
//     /* Signed multiplication overflow detection copied from Bitwuzla.
//      * See M.Gok, M.J. Schulte, P.I. Balzola, "Efficient integer multiplication
//      * overflow detection circuits", 2001.
//      * http://ieeexplore.ieee.org/document/987767 */
//     let (mut x, mut y) = (terms[0].clone(), terms[1].clone());
//     let k = x.len();
//     if k == 1 {
//         return TermVec::from([&x[0] & &y[0]]);
//     }
//     let (sgnx, sgny) = (x.last().unwrap().clone(), y.last().unwrap().clone());
//     x.push(sgnx.clone()); // sign extend by 1 bit
//     y.push(sgny.clone());
//     let mul = mul_bitblast(&[x.clone(), y.clone()]);
//     if k == 2 {
//         return TermVec::from([&mul[2] ^ &mul[1]]);
//     }

//     x.iter_mut().for_each(|b| *b = &*b ^ &sgnx);
//     y.iter_mut().for_each(|b| *b = &*b ^ &sgny);
//     let mut ppc = x[k - 2].clone();
//     let mut res = &ppc & &y[1];
//     for i in 1..k - 2 {
//         ppc = &ppc | &x[k - 2 - i];
//         res = &res | (&ppc & &y[i + 1]);
//     }
//     TermVec::from([&res | (&mul[k] ^ &mul[k - 1])])
// }

fn scgate_co(r: &Term, d: &Term, ci: &Term) -> Term {
    let d_or_ci = d | ci;
    let d_and_ci = d & ci;
    let m = &d_or_ci & r;
    d_and_ci | &m
}
fn scgate_s(r: &Term, d: &Term, ci: &Term, q: &Term) -> Term {
    let d_or_ci = d | ci;
    let d_and_ci = d & ci;
    let t1 = &d_or_ci & !&d_and_ci;
    let t2 = &t1 & q;
    let t2_or_r = &t2 | r;
    let t2_and_r = &t2 & r;
    &t2_or_r & !&t2_and_r
}

fn udiv_urem_bitblast(a: &TermVec, din: &TermVec) -> (TermVec, TermVec) {
    let nd: Vec<Term> = din.iter().map(|t| !t).collect();
    let size = a.len();
    let mut s = vec![vec![Term::bool_const(false); size + 1]; size + 1];
    let mut c = vec![vec![Term::bool_const(false); size + 1]; size + 1];
    let mut q = TermVec::new();

    for j in 0..size {
        c[j][0] = Term::bool_const(true);
        s[j][0] = a[size - j - 1].clone();
        for (i, ndi) in nd.iter().enumerate().take(size) {
            c[j][i + 1] = scgate_co(&s[j][i], ndi, &c[j][i]);
        }
        q.push(&c[j][size] | &s[j][size]);
        for (i, ndi) in nd.iter().enumerate().take(size) {
            s[j + 1][i + 1] = scgate_s(&s[j][i], ndi, &c[j][i], &q[j]);
        }
    }
    q.reverse(); // quotients come MSB first
    (q, TermVec::from(s[size][1..=size].to_vec()))
}

define_core_op!(Udiv, 2, bitblast: udiv_bitblast, simplify: udiv_simplify, simulate: udiv_simulate);
fn udiv_bitblast(terms: &[TermVec]) -> TermVec {
    let (q, _) = udiv_urem_bitblast(&terms[0], &terms[1]);
    q
}

fn udiv_simplify(_terms: &[Term]) -> TermResult {
    // let (x, _y) = (&terms[0], &terms[1]);
    // if let Some(xc) = x.try_bv_const() {
    //     if xc.is_zero() {
    //         return Some(x.clone());
    //     }
    // }
    None
}

define_core_op!(Urem, 2, bitblast: urem_bitblast, simulate: urem_simulate);
fn urem_bitblast(terms: &[TermVec]) -> TermVec {
    let (_, r) = udiv_urem_bitblast(&terms[0], &terms[1]);
    r
}

define_core_op!(Neg, 1, bitblast: neg_bitblast, simulate: neg_simulate);
fn neg_bitblast(terms: &[TermVec]) -> TermVec {
    let x = &terms[0];
    let mut res = TermVec::new();
    res.push(x[0].clone());
    let mut c = !&x[0];
    for i in 1..x.len() {
        res.push((&c & &x[i]) | (!&c & !&x[i]));
        c = &c & !&x[i];
    }
    res
}

define_core_op!(Sdiv, 2, bitblast: sdiv_bitblast, simulate: sdiv_simulate);
fn sdiv_bitblast(terms: &[TermVec]) -> TermVec {
    let (x, y) = (&terms[0], &terms[1]);
    let w = x.len();
    if w == 1 {
        return TermVec::from([!(!&x[0] & &y[0])]);
        // TermVec::from([&x[0] | !&y[0]])
    }
    let (sgnx, sgny) = (x.last().unwrap(), y.last().unwrap());
    let xor = sgnx ^ sgny;
    let negx = neg_bitblast(terms);
    let negy = neg_bitblast(&terms[1..]);
    let cndx = negx
        .iter()
        .zip(x.iter())
        .map(|(n, p)| Term::new_op(Ite, [sgnx, n, p]))
        .collect();
    let cndy = negy
        .iter()
        .zip(y.iter())
        .map(|(n, p)| Term::new_op(Ite, [sgny, n, p]))
        .collect();
    let udiv = udiv_bitblast(&[cndx, cndy]);
    let neg_udiv = neg_bitblast(slice::from_ref(&udiv));
    neg_udiv
        .iter()
        .zip(udiv.iter())
        .map(|(n, p)| Term::new_op(Ite, [&xor, n, p]))
        .collect()
}

define_core_op!(Srem, 2, bitblast: srem_bitblast, simulate: srem_simulate);
fn srem_bitblast(terms: &[TermVec]) -> TermVec {
    let (x, y) = (&terms[0], &terms[1]);
    let w = x.len();
    if w == 1 {
        return TermVec::from([&x[0] & !&y[0]]);
    }
    let (sgnx, sgny) = (x.last().unwrap(), y.last().unwrap());
    let negx = neg_bitblast(terms);
    let negy = neg_bitblast(&terms[1..]);
    let cndx = negx
        .iter()
        .zip(x.iter())
        .map(|(n, p)| Term::new_op(Ite, [sgnx, n, p]))
        .collect();
    let cndy = negy
        .iter()
        .zip(y.iter())
        .map(|(n, p)| Term::new_op(Ite, [sgny, n, p]))
        .collect();
    let urem = urem_bitblast(&[cndx, cndy]);
    let neg_urem = neg_bitblast(slice::from_ref(&urem));
    neg_urem
        .iter()
        .zip(urem.iter())
        .map(|(n, p)| Term::new_op(Ite, [sgnx, n, p]))
        .collect()
}

define_core_op!(Smod, 2, bitblast: smod_bitblast, simulate: smod_simulate);
fn smod_bitblast(terms: &[TermVec]) -> TermVec {
    let (x, y) = (&terms[0], &terms[1]);
    let w = x.len();
    if w == 1 {
        return TermVec::from([&x[0] & !&y[0]]);
    }
    let (sgnx, sgny) = (x.last().unwrap(), y.last().unwrap());
    let negx = neg_bitblast(terms);
    let negy = neg_bitblast(&terms[1..]);
    let cndx = negx
        .iter()
        .zip(x.iter())
        .map(|(n, p)| Term::new_op(Ite, [sgnx, n, p]))
        .collect();
    let cndy = negy
        .iter()
        .zip(y.iter())
        .map(|(n, p)| Term::new_op(Ite, [sgny, n, p]))
        .collect();
    let posi_urem = urem_bitblast(&[cndx, cndy]);
    let nega_urem = neg_bitblast(slice::from_ref(&posi_urem));
    let nega_urem_add = add_bitblast(&[nega_urem.clone(), y.clone()]);
    let posi_urem_add = add_bitblast(&[posi_urem.clone(), y.clone()]);
    let urem_is0 = Term::new_op(Ands, posi_urem.iter().map(|t| !t));

    let both_posi = !sgnx & !sgny;
    let nega_posi = sgnx & !sgny;
    let posi_nega = !sgnx & sgny;
    let posi_nega = posi_urem_add
        .iter()
        .zip(nega_urem.iter())
        .map(|(a, b)| Term::new_op(Ite, [&posi_nega, a, b]));
    let nega_posi = nega_urem_add
        .iter()
        .zip(posi_nega)
        .map(|(a, b)| Term::new_op(Ite, [&nega_posi, a, &b]));
    let both_posi = &urem_is0 | &both_posi;
    let both_posi = posi_urem
        .iter()
        .zip(nega_posi)
        .map(|(a, b)| Term::new_op(Ite, [&both_posi, a, &b]));
    both_posi.collect()
}

// define_core_op!(Sdivo, 2, sort: bool_sort, bitblast: sdivo_bitblast);
// fn sdivo_bitblast(terms: &[TermVec]) -> TermVec {
//     let div_by0 = Term::new_op(Ands, terms[1].iter().map(|t| !t));
//     let w = terms[0].len();
//     assert!(w == terms[1].len());
//     let t = if w == 1 {
//         Term::bool_const(true)
//     } else {
//         Term::new_op(Ands, terms[0][0..w - 1].iter().map(|t| !t))
//     };
//     let mneg_div_neg1 = Term::new_op(Ands, &terms[1]) // -1
//         & t
//         & &terms[0][w - 1]; // INT_MIN
//     TermVec::from([div_by0 | mneg_div_neg1])
// }

define_core_op!(Read, 2, sort: read_sort, bitblast: read_bitblast, simulate: read_simulate);
fn read_sort(terms: &[Term]) -> Sort {
    let (_, e) = terms[0].sort().array();
    Sort::Bv(e)
}

fn onehot_rec(idx: usize, x: &[Term], res: &mut [Term]) {
    let len = 1_usize.checked_shl(idx as u32).unwrap();
    debug_assert!(res.len() == len.checked_mul(2).unwrap());
    res[0] = &res[0] & !&x[idx];
    for i in 0..len {
        res[i] = res[0].clone();
    }
    res[len] = &res[len] & &x[idx];
    for i in len..res.len() {
        res[i] = res[len].clone();
    }
    if idx == 0 {
        return;
    }
    onehot_rec(idx - 1, x, &mut res[0..len]);
    onehot_rec(idx - 1, x, &mut res[len..]);
}

fn onehot_encode(x: &[Term]) -> TermVec {
    let len = 1_usize.checked_shl(x.len() as u32).unwrap();
    let mut res = vec![Term::bool_const(true); len];
    onehot_rec(x.len() - 1, x, &mut res);
    TermVec::from(res)
}

fn read_bitblast(terms: &[TermVec]) -> TermVec {
    let (array, index) = (&terms[0], &terms[1]);
    let index_len = index.len();
    let array_len = array.len();
    let index_range = 1_usize.checked_shl(index_len as u32).unwrap();
    let element_len = array_len / index_range;
    let onehot = onehot_encode(index);
    let mut res = TermVec::new();
    for i in 0..element_len {
        let mut r = Term::bool_const(false);
        for j in 0..index_range {
            r = onehot[j].ite(&array[element_len * j + i], &r);
        }
        res.push(r);
    }
    res
}

define_core_op!(Write, 3, bitblast: write_bitblast, simulate: write_simulate);
fn write_bitblast(terms: &[TermVec]) -> TermVec {
    let (array, index, value) = (&terms[0], &terms[1], &terms[2]);
    let index_len = index.len();
    let array_len = array.len();
    let index_range = 1_usize.checked_shl(index_len as u32).unwrap();
    let element_len = array_len / index_range;
    let onehot = onehot_encode(index);
    let mut res = array.clone();
    for i in 0..element_len {
        for j in 0..index_range {
            let r = &mut res[element_len * j + i];
            *r = onehot[j].ite(&value[i], &r);
        }
    }
    res
}
