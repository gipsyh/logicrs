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
    let val = GHashMap::new();

    assert_bv_eq(&t.simulate(&val), "1");
    assert_bv_eq(&f.simulate(&val), "0");
}

#[test]
fn test_simulate_var_default() {
    // Variable not in val should default to X
    let x = Term::new_var(Sort::Bv(4));
    let val = GHashMap::new();

    assert_bv_eq(&x.simulate(&val), "xxxx");
}

#[test]
fn test_simulate_var_with_value() {
    let x = Term::new_var(Sort::Bv(4));
    let mut val = GHashMap::new();
    val.insert(x.clone(), bv_val("1010"));

    assert_bv_eq(&x.simulate(&val), "1010");
}

#[test]
fn test_simulate_not() {
    let x = Term::new_var(Sort::Bv(4));
    let not_x = !&x;

    let mut val = GHashMap::new();
    val.insert(x.clone(), bv_val("1010"));

    assert_bv_eq(&not_x.simulate(&val), "0101");
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

    assert_bv_eq(&and_xy.simulate(&val), "1000");
    assert_bv_eq(&or_xy.simulate(&val), "1110");
    assert_bv_eq(&xor_xy.simulate(&val), "0110");
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
    assert_bv_eq(&add_xy.simulate(&val), "1000");
    // 5 - 3 = 2 (0010)
    assert_bv_eq(&sub_xy.simulate(&val), "0010");
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
    assert_bv_eq(&ite.simulate(&val), "1111");

    // Test when condition is false
    val.insert(c.clone(), bv_val("0"));
    assert_bv_eq(&ite.simulate(&val), "0000");
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
    assert_bv_eq(&expr.simulate(&val), "1001");
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
    assert_bv_eq(&and_xy.simulate(&val), "1x00");
}
