use super::{Sort, Term, Value};
use crate::LboolVec;
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
fn test_simulate_add_sub() {
    let x = Term::new_var(Sort::Bv(4));
    let y = Term::new_var(Sort::Bv(4));

    let add_xy = &x + &y;
    let sub_xy = &x - &y;

    let mut val = GHashMap::new();
    // x = 5 (0101), y = 3 (0011)
    val.insert(x.clone(), bv_val("0101"));
    val.insert(y.clone(), bv_val("0011"));

    // 5 + 3 = 8 (1000)
    assert_bv_eq(&add_xy.simulate(&mut val), "1000");
    // 5 - 3 = 2 (0010)
    assert_bv_eq(&sub_xy.simulate(&mut val), "0010");
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
fn test_simplify_not_not() {
    let x = Term::new_var(Sort::Bv(1));
    let expr = !!&x;
    let mut map = GHashMap::new();
    assert_eq!(expr.simplify(&mut map), x);
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
