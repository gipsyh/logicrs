use super::op::FolOp;
use super::simplify::SimplifyCtx;
use super::{Sort, Term, Value};
use crate::LboolVec;
use crate::OptLevel;
use giputils::bitvec::BitVec;
use giputils::hash::GHashMap;

fn bv_val(s: &str) -> Value {
    Value::Bv(LboolVec::from(s))
}

fn assert_bv_eq(v: &Value, expected: &str) {
    let bv = v.as_bv().unwrap();
    let expected_bv = LboolVec::from(expected);
    assert_eq!(bv, &expected_bv, "expected {}, got {}", expected, bv);
}

#[test]
fn test_simulate_const() {
    let t = Term::bool_const(true);
    let f = Term::bool_const(false);
    let mut val = GHashMap::new();

    assert_bv_eq(&t.simulate(&mut val), "1");
    assert_bv_eq(&f.simulate(&mut val), "0");
}

#[test]
fn test_simulate_var_default() {
    // Variable not in val should default to X
    let x = Term::new_var(Sort::Bv(4));
    let mut val = GHashMap::new();

    assert_bv_eq(&x.simulate(&mut val), "xxxx");
}

#[test]
fn test_simulate_var_with_value() {
    let x = Term::new_var(Sort::Bv(4));
    let mut val = GHashMap::new();
    val.insert(x.clone(), bv_val("1010"));

    assert_bv_eq(&x.simulate(&mut val), "1010");
}

#[test]
fn test_simulate_not() {
    let x = Term::new_var(Sort::Bv(4));
    let not_x = !&x;

    let mut val = GHashMap::new();
    val.insert(x.clone(), bv_val("1010"));

    assert_bv_eq(&not_x.simulate(&mut val), "0101");
}

#[test]
fn test_simulate_and_or_xor() {
    let x = Term::new_var(Sort::Bv(4));
    let y = Term::new_var(Sort::Bv(4));

    let and_xy = &x & &y;
    let or_xy = &x | &y;
    let xor_xy = &x ^ &y;

    let mut val = GHashMap::new();
    val.insert(x.clone(), bv_val("1100"));
    val.insert(y.clone(), bv_val("1010"));

    assert_bv_eq(&and_xy.simulate(&mut val), "1000");
    assert_bv_eq(&or_xy.simulate(&mut val), "1110");
    assert_bv_eq(&xor_xy.simulate(&mut val), "0110");
}

#[test]
fn test_simulate_ite() {
    let c = Term::new_var(Sort::Bv(1));
    let t = Term::new_var(Sort::Bv(4));
    let e = Term::new_var(Sort::Bv(4));

    let ite = c.ite(&t, &e);

    // Test when condition is true
    let mut val = GHashMap::new();
    val.insert(c.clone(), bv_val("1"));
    val.insert(t.clone(), bv_val("1111"));
    val.insert(e.clone(), bv_val("0000"));
    assert_bv_eq(&ite.simulate(&mut val), "1111");
}

#[test]
fn test_simulate_nested_expr() {
    // Test: (x & y) | (!x & z)
    let x = Term::new_var(Sort::Bv(4));
    let y = Term::new_var(Sort::Bv(4));
    let z = Term::new_var(Sort::Bv(4));

    let expr = (&x & &y) | (!&x & &z);

    let mut val = GHashMap::new();
    val.insert(x.clone(), bv_val("1100"));
    val.insert(y.clone(), bv_val("1010"));
    val.insert(z.clone(), bv_val("0101"));

    // x & y = 1000
    // !x = 0011
    // !x & z = 0001
    // result = 1001
    assert_bv_eq(&expr.simulate(&mut val), "1001");
}

#[test]
fn test_simulate_with_unknown() {
    let x = Term::new_var(Sort::Bv(4));
    let y = Term::new_var(Sort::Bv(4));

    let and_xy = &x & &y;

    let mut val = GHashMap::new();
    val.insert(x.clone(), bv_val("1x00"));
    val.insert(y.clone(), bv_val("1100"));

    // 1x00 & 1100 = 1x00 (x & 1 = x, x & 0 = 0)
    assert_bv_eq(&and_xy.simulate(&mut val), "1x00");
}

#[test]
fn test_simplify_and_or_identities() {
    let x = Term::new_var(Sort::Bv(1));

    let and_expr = Term::bool_const(true) & &x;
    let mut map = GHashMap::new();
    assert_eq!(and_expr.simplify(&mut map), x);

    let or_expr = Term::bool_const(false) | &x;
    let mut map = GHashMap::new();
    assert_eq!(or_expr.simplify(&mut map), x);

    // Commutative fallback: ordered rule expects constants on the left.
    let and_expr = &x & Term::bool_const(true);
    let mut map = GHashMap::new();
    assert_eq!(and_expr.simplify(&mut map), x);

    let or_expr = &x | Term::bool_const(false);
    let mut map = GHashMap::new();
    assert_eq!(or_expr.simplify(&mut map), x);
}

#[test]
fn test_simplify_xor_identities() {
    let x = Term::new_var(Sort::Bv(1));

    let xor0 = Term::bool_const(false) ^ &x;
    let mut map = GHashMap::new();
    assert_eq!(xor0.simplify(&mut map), x);

    let xor1 = Term::bool_const(true) ^ &x;
    let mut map = GHashMap::new();
    assert_eq!(xor1.simplify(&mut map), !x.clone());

    // Commutative fallback
    let xor0 = &x ^ Term::bool_const(false);
    let mut map = GHashMap::new();
    assert_eq!(xor0.simplify(&mut map), x);
}

#[test]
fn test_simplify_associative_constants() {
    let x = Term::new_var(Sort::Bv(4));
    let c3 = Term::bv_const(BitVec::from("0011"));
    let c5 = Term::bv_const(BitVec::from("0101"));
    let c6 = Term::bv_const(BitVec::from("0110"));
    let c8 = Term::bv_const(BitVec::from("1000"));

    let mut map = GHashMap::new();
    assert_eq!(((&x + &c3) + &c5).simplify(&mut map), &x + &c8);

    let mut map = GHashMap::new();
    assert_eq!(((&x ^ &c3) ^ &c5).simplify(&mut map), &x ^ &c6);

    let mut map = GHashMap::new();
    assert_eq!(
        ((&x & &c3) & &c5).simplify(&mut map),
        &x & &Term::bv_const(BitVec::from("0001"))
    );
}

#[test]
fn test_simplify_not_not() {
    let x = Term::new_var(Sort::Bv(1));
    let expr = !!&x;
    let mut map = GHashMap::new();
    assert_eq!(expr.simplify(&mut map), x);
}

#[test]
fn test_simplify_ite_same_nested_condition() {
    let ctx = SimplifyCtx::new(OptLevel::O3);
    let c = Term::new_var(Sort::bool());
    let x = Term::new_var(Sort::Bv(8));
    let y = Term::new_var(Sort::Bv(8));
    let z = Term::new_var(Sort::Bv(8));

    let mut map = GHashMap::new();
    assert_eq!(
        c.ite(c.ite(&x, &y), &z).simplify_with_ctx(&ctx, &mut map),
        c.ite(&x, &z)
    );

    let mut map = GHashMap::new();
    assert_eq!(
        c.ite(&x, c.ite(&y, &z)).simplify_with_ctx(&ctx, &mut map),
        c.ite(&x, &z)
    );
}

#[test]
fn test_simplify_ite_nested_shared_branch() {
    let ctx = SimplifyCtx::new(OptLevel::O3);
    let c = Term::new_var(Sort::bool());
    let d = Term::new_var(Sort::bool());
    let x = Term::new_var(Sort::Bv(8));
    let y = Term::new_var(Sort::Bv(8));

    let mut map = GHashMap::new();
    assert_eq!(
        c.ite(d.ite(&x, &y), &y).simplify_with_ctx(&ctx, &mut map),
        (&c & &d).ite(&x, &y)
    );

    let mut map = GHashMap::new();
    assert_eq!(
        c.ite(d.ite(&y, &x), &y).simplify_with_ctx(&ctx, &mut map),
        (&c & !&d).ite(&x, &y)
    );

    let mut map = GHashMap::new();
    assert_eq!(
        c.ite(&x, d.ite(&x, &y)).simplify_with_ctx(&ctx, &mut map),
        (&c | &d).ite(&x, &y)
    );

    let mut map = GHashMap::new();
    assert_eq!(
        c.ite(&x, d.ite(&y, &x)).simplify_with_ctx(&ctx, &mut map),
        (&c | !&d).ite(&x, &y)
    );
}

fn signed_min(width: usize) -> Term {
    let mut c = BitVec::zero(width);
    c.set(width - 1, true);
    Term::bv_const(c)
}

fn signed_max(width: usize) -> Term {
    let mut c = BitVec::ones(width);
    c.set(width - 1, false);
    Term::bv_const(c)
}

#[test]
fn test_simplify_slt_identities() {
    let x = Term::new_var(Sort::Bv(8));
    let mut map = GHashMap::new();
    assert_eq!(
        x.op1(super::op::FolOp::Slt, &x).simplify(&mut map),
        Term::bool_const(false)
    );
}

#[test]
fn test_simplify_slt_signed_extremes() {
    let x = Term::new_var(Sort::Bv(8));
    let min = signed_min(8);
    let max = signed_max(8);

    let mut map = GHashMap::new();
    assert_eq!(
        min.op1(super::op::FolOp::Slt, &x).simplify(&mut map),
        !min.op1(super::op::FolOp::Eq, &x)
    );

    let mut map = GHashMap::new();
    assert_eq!(
        max.op1(super::op::FolOp::Slt, &x).simplify(&mut map),
        Term::bool_const(false)
    );

    let mut map = GHashMap::new();
    assert_eq!(
        x.op1(super::op::FolOp::Slt, &min).simplify(&mut map),
        Term::bool_const(false)
    );

    let mut map = GHashMap::new();
    assert_eq!(
        x.op1(super::op::FolOp::Slt, &max).simplify(&mut map),
        !x.op1(super::op::FolOp::Eq, &max)
    );
}

#[test]
fn test_simplify_slice_of_concat() {
    let hi = Term::new_var(Sort::Bv(4));
    let lo = Term::new_var(Sort::Bv(8));
    let concat = hi.concat(&lo);

    let mut map = GHashMap::new();
    assert_eq!(concat.slice(1, 3).simplify(&mut map), lo.slice(1, 3));

    let mut map = GHashMap::new();
    assert_eq!(concat.slice(8, 10).simplify(&mut map), hi.slice(0, 2));

    let mut map = GHashMap::new();
    let expected = hi.slice(0, 1).concat(lo.slice(6, 7));
    assert_eq!(concat.slice(6, 9).simplify(&mut map), expected);
}

#[test]
fn test_simplify_slice_pushdown_patterns() {
    let ctx = SimplifyCtx::new(OptLevel::O3);
    let c = Term::new_var(Sort::bool());
    let x = Term::new_var(Sort::Bv(8));
    let y = Term::new_var(Sort::Bv(8));

    let mut map = GHashMap::new();
    assert_eq!(
        c.ite(&x, &y).slice(2, 4).simplify_with_ctx(&ctx, &mut map),
        c.ite(x.slice(2, 4), y.slice(2, 4))
    );

    let mut map = GHashMap::new();
    assert_eq!(
        (&x & &y).slice(2, 4).simplify_with_ctx(&ctx, &mut map),
        x.slice(2, 4) & y.slice(2, 4)
    );

    let ext = Term::new_op(FolOp::Sext, [&x, &Term::bv_const(BitVec::zero(4))]);
    let mut map = GHashMap::new();
    assert_eq!(
        ext.slice(1, 3).simplify_with_ctx(&ctx, &mut map),
        x.slice(1, 3)
    );
}

#[test]
fn test_simplify_low_bit_arith_shift_patterns() {
    let ctx = SimplifyCtx::new(OptLevel::O3);
    let x = Term::new_var(Sort::Bv(8));
    let y = Term::new_var(Sort::Bv(8));

    let mut map = GHashMap::new();
    assert_eq!(
        (&x + &y).slice(0, 0).simplify_with_ctx(&ctx, &mut map),
        x.slice(0, 0) ^ y.slice(0, 0)
    );

    let mut map = GHashMap::new();
    assert_eq!(
        (&x - &y).slice(0, 0).simplify_with_ctx(&ctx, &mut map),
        x.slice(0, 0) ^ y.slice(0, 0)
    );

    let mut map = GHashMap::new();
    let sll = x.op1(FolOp::Sll, &y);
    assert_eq!(
        sll.slice(0, 0).simplify_with_ctx(&ctx, &mut map),
        y.op1(FolOp::Eq, y.mk_bv_const_zero()) & x.slice(0, 0)
    );
}

#[test]
fn test_simplify_nonnegative_slt_bound() {
    let x = Term::new_var(Sort::Bv(6));
    let zx = Term::bv_const(BitVec::zero(2)).concat(&x);
    let bound = Term::bv_const(BitVec::from("01000000"));
    let mut map = GHashMap::new();
    assert_eq!(
        zx.op1(FolOp::Slt, &bound).simplify(&mut map),
        Term::bool_const(true)
    );
}

#[test]
fn test_simplify_bool_mask_patterns() {
    let ctx = SimplifyCtx::new(OptLevel::O3);
    let c = Term::new_var(Sort::bool());
    let x = Term::new_var(Sort::Bv(8));
    let mask = c.ite(x.mk_bv_const_ones(), x.mk_bv_const_zero());

    let mut map = GHashMap::new();
    assert_eq!(
        (&x & &mask).simplify_with_ctx(&ctx, &mut map),
        c.ite(&x, x.mk_bv_const_zero())
    );

    let mut map = GHashMap::new();
    assert_eq!(
        (&x & !&mask).simplify_with_ctx(&ctx, &mut map),
        c.ite(x.mk_bv_const_zero(), &x)
    );

    let mut map = GHashMap::new();
    assert_eq!(
        (mask.op1(FolOp::Eq, x.mk_bv_const_zero())).simplify_with_ctx(&ctx, &mut map),
        !&c
    );

    let y = Term::new_var(Sort::Bv(8));
    let mut map = GHashMap::new();
    let masked_mux = ((&x & !&mask) | (&y & &mask)).simplify_with_ctx(&ctx, &mut map);
    assert_eq!(masked_mux, c.ite(&y, &x));

    let sext_mask = Term::new_op(FolOp::Sext, [&c, &Term::bv_const(BitVec::zero(7))]);
    let mut map = GHashMap::new();
    assert_eq!(
        (&x & &sext_mask).simplify_with_ctx(&ctx, &mut map),
        c.ite(&x, x.mk_bv_const_zero())
    );

    let mut map = GHashMap::new();
    assert_eq!(
        sext_mask
            .op1(FolOp::Eq, sext_mask.mk_bv_const_zero())
            .simplify_with_ctx(&ctx, &mut map),
        !&c
    );
}

#[test]
fn test_simplify_array_same_index_patterns() {
    let ctx = SimplifyCtx::new(OptLevel::O3);
    let c = Term::new_var(Sort::bool());
    let array = Term::new_var(Sort::Array(3, 8));
    let index = Term::new_var(Sort::Bv(3));
    let value = Term::new_var(Sort::Bv(8));
    let read = Term::new_op(FolOp::Read, [&array, &index]);
    let write = Term::new_op(FolOp::Write, [&array, &index, &value]);

    let mut map = GHashMap::new();
    assert_eq!(
        Term::new_op(FolOp::Read, [&write, &index]).simplify_with_ctx(&ctx, &mut map),
        value
    );

    let mut map = GHashMap::new();
    assert_eq!(
        Term::new_op(FolOp::Write, [&array, &index, &read]).simplify_with_ctx(&ctx, &mut map),
        array
    );

    let conditional_value = c.ite(&value, &read);
    let conditional_write = Term::new_op(FolOp::Write, [&array, &index, &conditional_value]);
    let mut map = GHashMap::new();
    assert_eq!(
        c.ite(&conditional_write, &array)
            .simplify_with_ctx(&ctx, &mut map),
        conditional_write
    );
}

// Regression tests for the Ult/Slt sort bug.
//
// Before the fix, FolOp::sort() returned terms[0].sort() (the operand width)
// for Ult and Slt instead of Sort::Bv(1).  The BTOR2 parser asserts that the
// sort computed by new_op matches the sort declared in the BTOR2 file; for any
// N-bit (N > 1) comparison this assertion would fire immediately on parse.
//
// Minimal reproducer BTOR2:
//   1 sort bitvec 1
//   2 sort bitvec 8
//   3 input 2 a
//   4 input 2 b
//   5 ult 1 3 4    ← panicked here before the fix
//   6 bad 5

#[test]
fn test_ult_result_sort_is_one_bit() {
    // Operands are 8-bit; result must be 1-bit regardless.
    let x = Term::new_var(Sort::Bv(8));
    let y = Term::new_var(Sort::Bv(8));
    let ult = x.op1(super::op::FolOp::Ult, &y);
    assert_eq!(
        ult.sort(),
        Sort::Bv(1),
        "ult of 8-bit operands must have sort bitvec 1"
    );
}

#[test]
fn test_slt_result_sort_is_one_bit() {
    let x = Term::new_var(Sort::Bv(8));
    let y = Term::new_var(Sort::Bv(8));
    let slt = x.op1(super::op::FolOp::Slt, &y);
    assert_eq!(
        slt.sort(),
        Sort::Bv(1),
        "slt of 8-bit operands must have sort bitvec 1"
    );
}

#[test]
fn test_ult_simulate() {
    // Strings are MSB-first; LboolVec::from reverses them to LSB-first internally.
    let x = Term::new_var(Sort::Bv(8));
    let y = Term::new_var(Sort::Bv(8));
    let ult = x.op1(super::op::FolOp::Ult, &y);

    // 5 < 10 → true
    let mut val = GHashMap::new();
    val.insert(x.clone(), bv_val("00000101")); // 5
    val.insert(y.clone(), bv_val("00001010")); // 10
    assert_bv_eq(&ult.simulate(&mut val), "1");

    // 10 < 5 → false
    let mut val = GHashMap::new();
    val.insert(x.clone(), bv_val("00001010")); // 10
    val.insert(y.clone(), bv_val("00000101")); // 5
    assert_bv_eq(&ult.simulate(&mut val), "0");

    // 5 < 5 → false (equal, not strictly less)
    let mut val = GHashMap::new();
    val.insert(x.clone(), bv_val("00000101")); // 5
    val.insert(y.clone(), bv_val("00000101")); // 5
    assert_bv_eq(&ult.simulate(&mut val), "0");
}

#[test]
fn test_slt_simulate() {
    let x = Term::new_var(Sort::Bv(8));
    let y = Term::new_var(Sort::Bv(8));
    let slt = x.op1(super::op::FolOp::Slt, &y);

    // -1 (0xFF) < 1 (0x01) → true (signed)
    let mut val = GHashMap::new();
    val.insert(x.clone(), bv_val("11111111")); // -1
    val.insert(y.clone(), bv_val("00000001")); //  1
    assert_bv_eq(&slt.simulate(&mut val), "1");

    // 1 < -1 → false (signed)
    let mut val = GHashMap::new();
    val.insert(x.clone(), bv_val("00000001")); //  1
    val.insert(y.clone(), bv_val("11111111")); // -1
    assert_bv_eq(&slt.simulate(&mut val), "0");

    // 5 < 10 → true (positive values, same as unsigned)
    let mut val = GHashMap::new();
    val.insert(x.clone(), bv_val("00000101")); // 5
    val.insert(y.clone(), bv_val("00001010")); // 10
    assert_bv_eq(&slt.simulate(&mut val), "1");
}
