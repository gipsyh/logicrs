use super::simulate::*;
use crate::LboolVec;
use crate::fol::Value;

fn bv(s: &str) -> Value {
    Value::Bv(LboolVec::from(s))
}

fn assert_bv_eq(v: &Value, expected: &str) {
    let bv = v.as_bv().unwrap();
    let expected_bv = LboolVec::from(expected);
    assert_eq!(bv, &expected_bv, "expected {}, got {}", expected, bv);
}

#[test]
fn test_not_simulate() {
    assert_bv_eq(&not_simulate(&[bv("0")]), "1");
    assert_bv_eq(&not_simulate(&[bv("1")]), "0");
    assert_bv_eq(&not_simulate(&[bv("1010")]), "0101");
    assert_bv_eq(&not_simulate(&[bv("11110000")]), "00001111");
    assert_bv_eq(&not_simulate(&[bv("x")]), "x");
    assert_bv_eq(&not_simulate(&[bv("1x0")]), "0x1");
}

#[test]
fn test_and_simulate() {
    assert_bv_eq(&and_simulate(&[bv("0"), bv("0")]), "0");
    assert_bv_eq(&and_simulate(&[bv("0"), bv("1")]), "0");
    assert_bv_eq(&and_simulate(&[bv("1"), bv("0")]), "0");
    assert_bv_eq(&and_simulate(&[bv("1"), bv("1")]), "1");
    assert_bv_eq(&and_simulate(&[bv("1010"), bv("1100")]), "1000");
    assert_bv_eq(&and_simulate(&[bv("1111"), bv("0101")]), "0101");
    assert_bv_eq(&and_simulate(&[bv("1x0"), bv("110")]), "1x0");
    assert_bv_eq(&and_simulate(&[bv("x"), bv("0")]), "0");
    assert_bv_eq(&and_simulate(&[bv("x"), bv("1")]), "x");
}

#[test]
fn test_ands_simulate() {
    assert_bv_eq(&ands_simulate(&[bv("1111")]), "1111");
    assert_bv_eq(&ands_simulate(&[bv("1111"), bv("1010")]), "1010");
    assert_bv_eq(
        &ands_simulate(&[bv("1111"), bv("1010"), bv("1100")]),
        "1000",
    );
}

#[test]
fn test_or_simulate() {
    assert_bv_eq(&or_simulate(&[bv("0"), bv("0")]), "0");
    assert_bv_eq(&or_simulate(&[bv("0"), bv("1")]), "1");
    assert_bv_eq(&or_simulate(&[bv("1"), bv("0")]), "1");
    assert_bv_eq(&or_simulate(&[bv("1"), bv("1")]), "1");
    assert_bv_eq(&or_simulate(&[bv("1010"), bv("1100")]), "1110");
    assert_bv_eq(&or_simulate(&[bv("0000"), bv("0101")]), "0101");
    assert_bv_eq(&or_simulate(&[bv("x"), bv("1")]), "1");
    assert_bv_eq(&or_simulate(&[bv("x"), bv("0")]), "x");
}

#[test]
fn test_ors_simulate() {
    assert_bv_eq(&ors_simulate(&[bv("0000")]), "0000");
    assert_bv_eq(&ors_simulate(&[bv("0000"), bv("1010")]), "1010");
    assert_bv_eq(&ors_simulate(&[bv("0001"), bv("0010"), bv("0100")]), "0111");
}

#[test]
fn test_xor_simulate() {
    assert_bv_eq(&xor_simulate(&[bv("0"), bv("0")]), "0");
    assert_bv_eq(&xor_simulate(&[bv("0"), bv("1")]), "1");
    assert_bv_eq(&xor_simulate(&[bv("1"), bv("0")]), "1");
    assert_bv_eq(&xor_simulate(&[bv("1"), bv("1")]), "0");
    assert_bv_eq(&xor_simulate(&[bv("1010"), bv("1100")]), "0110");
    assert_bv_eq(&xor_simulate(&[bv("1111"), bv("1111")]), "0000");
    assert_bv_eq(&xor_simulate(&[bv("x"), bv("0")]), "x");
    assert_bv_eq(&xor_simulate(&[bv("x"), bv("1")]), "x");
}

#[test]
fn test_eq_simulate() {
    assert_bv_eq(&eq_simulate(&[bv("0"), bv("0")]), "1");
    assert_bv_eq(&eq_simulate(&[bv("1"), bv("1")]), "1");
    assert_bv_eq(&eq_simulate(&[bv("0"), bv("1")]), "0");
    assert_bv_eq(&eq_simulate(&[bv("1010"), bv("1010")]), "1");
    assert_bv_eq(&eq_simulate(&[bv("1010"), bv("1011")]), "0");
    assert_bv_eq(&eq_simulate(&[bv("x"), bv("0")]), "x");
    assert_bv_eq(&eq_simulate(&[bv("1x"), bv("1x")]), "x");
}

#[test]
fn test_ult_simulate() {
    // 0 < 0 = false
    assert_bv_eq(&ult_simulate(&[bv("0"), bv("0")]), "0");
    // 0 < 1 = true
    assert_bv_eq(&ult_simulate(&[bv("0"), bv("1")]), "1");
    // 1 < 0 = false
    assert_bv_eq(&ult_simulate(&[bv("1"), bv("0")]), "0");
    // 1 < 1 = false
    assert_bv_eq(&ult_simulate(&[bv("1"), bv("1")]), "0");
    // 0010 (2) < 0101 (5) = true
    assert_bv_eq(&ult_simulate(&[bv("0010"), bv("0101")]), "1");
    // 0101 (5) < 0010 (2) = false
    assert_bv_eq(&ult_simulate(&[bv("0101"), bv("0010")]), "0");
    // 1111 (15) < 0001 (1) = false
    assert_bv_eq(&ult_simulate(&[bv("1111"), bv("0001")]), "0");
}

#[test]
fn test_slt_simulate() {
    // Signed comparison (2's complement)
    // 0 < 0 = false
    assert_bv_eq(&slt_simulate(&[bv("0000"), bv("0000")]), "0");
    // 1 < -1 (0001 < 1111) = false (1 < -1 is false)
    assert_bv_eq(&slt_simulate(&[bv("0001"), bv("1111")]), "0");
    // -1 < 1 (1111 < 0001) = true (-1 < 1 is true)
    assert_bv_eq(&slt_simulate(&[bv("1111"), bv("0001")]), "1");
    // -2 < -1 (1110 < 1111) = true
    assert_bv_eq(&slt_simulate(&[bv("1110"), bv("1111")]), "1");
    // 3 < 5 (0011 < 0101) = true
    assert_bv_eq(&slt_simulate(&[bv("0011"), bv("0101")]), "1");
}

#[test]
fn test_sll_simulate() {
    // 0001 << 0 = 0001
    assert_bv_eq(&sll_simulate(&[bv("0001"), bv("0000")]), "0001");
    // 0001 << 1 = 0010
    assert_bv_eq(&sll_simulate(&[bv("0001"), bv("0001")]), "0010");
    // 0001 << 2 = 0100
    assert_bv_eq(&sll_simulate(&[bv("0001"), bv("0010")]), "0100");
    // 0001 << 3 = 1000
    assert_bv_eq(&sll_simulate(&[bv("0001"), bv("0011")]), "1000");
    // 0001 << 4 = 0000 (shifted out)
    assert_bv_eq(&sll_simulate(&[bv("0001"), bv("0100")]), "0000");
    // 1010 << 1 = 0100
    assert_bv_eq(&sll_simulate(&[bv("1010"), bv("0001")]), "0100");
}

#[test]
fn test_srl_simulate() {
    // 1000 >> 0 = 1000
    assert_bv_eq(&srl_simulate(&[bv("1000"), bv("0000")]), "1000");
    // 1000 >> 1 = 0100
    assert_bv_eq(&srl_simulate(&[bv("1000"), bv("0001")]), "0100");
    // 1000 >> 2 = 0010
    assert_bv_eq(&srl_simulate(&[bv("1000"), bv("0010")]), "0010");
    // 1000 >> 3 = 0001
    assert_bv_eq(&srl_simulate(&[bv("1000"), bv("0011")]), "0001");
    // 1000 >> 4 = 0000 (shifted out)
    assert_bv_eq(&srl_simulate(&[bv("1000"), bv("0100")]), "0000");
    // 1010 >> 1 = 0101
    assert_bv_eq(&srl_simulate(&[bv("1010"), bv("0001")]), "0101");
}

#[test]
fn test_sra_simulate() {
    // Positive number: 0100 >> 1 = 0010
    assert_bv_eq(&sra_simulate(&[bv("0100"), bv("0001")]), "0010");
    // Negative number: 1000 >> 1 = 1100 (sign extended)
    assert_bv_eq(&sra_simulate(&[bv("1000"), bv("0001")]), "1100");
    // 1000 >> 2 = 1110
    assert_bv_eq(&sra_simulate(&[bv("1000"), bv("0010")]), "1110");
    // 1000 >> 3 = 1111
    assert_bv_eq(&sra_simulate(&[bv("1000"), bv("0011")]), "1111");
    // 1000 >> 4 = 1111 (all sign bits)
    assert_bv_eq(&sra_simulate(&[bv("1000"), bv("0100")]), "1111");
}

#[test]
fn test_rol_simulate() {
    // 0001 rol 0 = 0001
    assert_bv_eq(&rol_simulate(&[bv("0001"), bv("0000")]), "0001");
    // 0001 rol 1 = 0010
    assert_bv_eq(&rol_simulate(&[bv("0001"), bv("0001")]), "0010");
    // 0001 rol 2 = 0100
    assert_bv_eq(&rol_simulate(&[bv("0001"), bv("0010")]), "0100");
    // 0001 rol 3 = 1000
    assert_bv_eq(&rol_simulate(&[bv("0001"), bv("0011")]), "1000");
    // 0001 rol 4 = 0001 (wrap around)
    assert_bv_eq(&rol_simulate(&[bv("0001"), bv("0100")]), "0001");
    // 1001 rol 1 = 0011
    assert_bv_eq(&rol_simulate(&[bv("1001"), bv("0001")]), "0011");
}

#[test]
fn test_ror_simulate() {
    // 1000 ror 0 = 1000
    assert_bv_eq(&ror_simulate(&[bv("1000"), bv("0000")]), "1000");
    // 1000 ror 1 = 0100
    assert_bv_eq(&ror_simulate(&[bv("1000"), bv("0001")]), "0100");
    // 1000 ror 2 = 0010
    assert_bv_eq(&ror_simulate(&[bv("1000"), bv("0010")]), "0010");
    // 1000 ror 3 = 0001
    assert_bv_eq(&ror_simulate(&[bv("1000"), bv("0011")]), "0001");
    // 1000 ror 4 = 1000 (wrap around)
    assert_bv_eq(&ror_simulate(&[bv("1000"), bv("0100")]), "1000");
    // 0001 ror 1 = 1000
    assert_bv_eq(&ror_simulate(&[bv("0001"), bv("0001")]), "1000");
}

#[test]
fn test_ite_simulate() {
    // if 1 then 1010 else 0101 = 1010
    assert_bv_eq(&ite_simulate(&[bv("1"), bv("1010"), bv("0101")]), "1010");
    // if 0 then 1010 else 0101 = 0101
    assert_bv_eq(&ite_simulate(&[bv("0"), bv("1010"), bv("0101")]), "0101");
    // if x then 1111 else 1111 = 1111 (same value)
    assert_bv_eq(&ite_simulate(&[bv("x"), bv("1111"), bv("1111")]), "1111");
    // if x then 1010 else 0101 = xxxx (different values)
    assert_bv_eq(&ite_simulate(&[bv("x"), bv("1010"), bv("0101")]), "xxxx");
    // if x then 1010 else 1000 = 10x0 (partial match)
    assert_bv_eq(&ite_simulate(&[bv("x"), bv("1010"), bv("1000")]), "10x0");
}

#[test]
fn test_concat_simulate() {
    // concat(11, 00) = 1100
    assert_bv_eq(&concat_simulate(&[bv("11"), bv("00")]), "1100");
    // concat(1, 0) = 10
    assert_bv_eq(&concat_simulate(&[bv("1"), bv("0")]), "10");
    // concat(1010, 0101) = 10100101
    assert_bv_eq(&concat_simulate(&[bv("1010"), bv("0101")]), "10100101");
    // concat(x, 1) = x1
    assert_bv_eq(&concat_simulate(&[bv("x"), bv("1")]), "x1");
}

#[test]
fn test_sext_simulate() {
    // sext(0100, 4) = 00000100 (positive, extend with 0s)
    assert_bv_eq(&sext_simulate(&[bv("0100"), bv("0000")]), "00000100");
    // sext(1100, 4) = 11111100 (negative, extend with 1s)
    assert_bv_eq(&sext_simulate(&[bv("1100"), bv("0000")]), "11111100");
    // sext(1, 3) = 1111 (negative 1-bit, extend with 1s)
    assert_bv_eq(&sext_simulate(&[bv("1"), bv("000")]), "1111");
    // sext(0, 3) = 0000
    assert_bv_eq(&sext_simulate(&[bv("0"), bv("000")]), "0000");
}

#[test]
fn test_slice_simulate() {
    // slice(10110100, high=5, low=2) = 1101 (bits 2,3,4,5)
    // Using bv_len encoding: high index represented by len, low index represented by len
    assert_bv_eq(
        &slice_simulate(&[bv("10110100"), bv("00000"), bv("00")]),
        "1101",
    );
    // slice(11110000, high=7, low=4) = 1111
    assert_bv_eq(
        &slice_simulate(&[bv("11110000"), bv("0000000"), bv("0000")]),
        "1111",
    );
    // slice(10101010, high=3, low=0) = 1010
    assert_bv_eq(
        &slice_simulate(&[bv("10101010"), bv("000"), bv("")]),
        "1010",
    );
}

#[test]
fn test_redxor_simulate() {
    // redxor(0000) = 0
    assert_bv_eq(&redxor_simulate(&[bv("0000")]), "0");
    // redxor(0001) = 1
    assert_bv_eq(&redxor_simulate(&[bv("0001")]), "1");
    // redxor(0011) = 0
    assert_bv_eq(&redxor_simulate(&[bv("0011")]), "0");
    // redxor(0111) = 1
    assert_bv_eq(&redxor_simulate(&[bv("0111")]), "1");
    // redxor(1111) = 0
    assert_bv_eq(&redxor_simulate(&[bv("1111")]), "0");
    // redxor(1010) = 0
    assert_bv_eq(&redxor_simulate(&[bv("1010")]), "0");
    // redxor(1011) = 1
    assert_bv_eq(&redxor_simulate(&[bv("1011")]), "1");
}

#[test]
fn test_add_simulate() {
    // 0 + 0 = 0
    assert_bv_eq(&add_simulate(&[bv("0000"), bv("0000")]), "0000");
    // 1 + 1 = 2
    assert_bv_eq(&add_simulate(&[bv("0001"), bv("0001")]), "0010");
    // 5 + 3 = 8
    assert_bv_eq(&add_simulate(&[bv("0101"), bv("0011")]), "1000");
    // 15 + 1 = 0 (overflow)
    assert_bv_eq(&add_simulate(&[bv("1111"), bv("0001")]), "0000");
    // 7 + 7 = 14
    assert_bv_eq(&add_simulate(&[bv("0111"), bv("0111")]), "1110");
}

#[test]
fn test_sub_simulate() {
    // 0 - 0 = 0
    assert_bv_eq(&sub_simulate(&[bv("0000"), bv("0000")]), "0000");
    // 2 - 1 = 1
    assert_bv_eq(&sub_simulate(&[bv("0010"), bv("0001")]), "0001");
    // 5 - 3 = 2
    assert_bv_eq(&sub_simulate(&[bv("0101"), bv("0011")]), "0010");
    // 0 - 1 = 15 (underflow, wrap around)
    assert_bv_eq(&sub_simulate(&[bv("0000"), bv("0001")]), "1111");
    // 8 - 8 = 0
    assert_bv_eq(&sub_simulate(&[bv("1000"), bv("1000")]), "0000");
}

#[test]
fn test_mul_simulate() {
    // 0 * 0 = 0
    assert_bv_eq(&mul_simulate(&[bv("0000"), bv("0000")]), "0000");
    // 1 * 1 = 1
    assert_bv_eq(&mul_simulate(&[bv("0001"), bv("0001")]), "0001");
    // 2 * 3 = 6
    assert_bv_eq(&mul_simulate(&[bv("0010"), bv("0011")]), "0110");
    // 3 * 3 = 9
    assert_bv_eq(&mul_simulate(&[bv("0011"), bv("0011")]), "1001");
    // 4 * 4 = 16 -> 0 (overflow, only lower 4 bits)
    assert_bv_eq(&mul_simulate(&[bv("0100"), bv("0100")]), "0000");
    // 5 * 2 = 10
    assert_bv_eq(&mul_simulate(&[bv("0101"), bv("0010")]), "1010");
}

#[test]
fn test_neg_simulate() {
    // -0 = 0
    assert_bv_eq(&neg_simulate(&[bv("0000")]), "0000");
    // -1 = 15 (0001 -> 1111)
    assert_bv_eq(&neg_simulate(&[bv("0001")]), "1111");
    // -2 = 14 (0010 -> 1110)
    assert_bv_eq(&neg_simulate(&[bv("0010")]), "1110");
    // -(-1) = 1 (1111 -> 0001)
    assert_bv_eq(&neg_simulate(&[bv("1111")]), "0001");
    // -8 = 8 (1000 -> 1000, special case for min value)
    assert_bv_eq(&neg_simulate(&[bv("1000")]), "1000");
}

#[test]
fn test_udiv_simulate() {
    // 6 / 2 = 3
    assert_bv_eq(&udiv_simulate(&[bv("0110"), bv("0010")]), "0011");
    // 8 / 2 = 4
    assert_bv_eq(&udiv_simulate(&[bv("1000"), bv("0010")]), "0100");
    // 9 / 3 = 3
    assert_bv_eq(&udiv_simulate(&[bv("1001"), bv("0011")]), "0011");
    // 7 / 2 = 3 (integer division)
    assert_bv_eq(&udiv_simulate(&[bv("0111"), bv("0010")]), "0011");
    // 0 / 5 = 0
    assert_bv_eq(&udiv_simulate(&[bv("0000"), bv("0101")]), "0000");
}

#[test]
fn test_urem_simulate() {
    // 6 % 2 = 0
    assert_bv_eq(&urem_simulate(&[bv("0110"), bv("0010")]), "0000");
    // 7 % 2 = 1
    assert_bv_eq(&urem_simulate(&[bv("0111"), bv("0010")]), "0001");
    // 9 % 4 = 1
    assert_bv_eq(&urem_simulate(&[bv("1001"), bv("0100")]), "0001");
    // 10 % 3 = 1
    assert_bv_eq(&urem_simulate(&[bv("1010"), bv("0011")]), "0001");
    // 0 % 5 = 0
    assert_bv_eq(&urem_simulate(&[bv("0000"), bv("0101")]), "0000");
}

#[test]
fn test_sdiv_simulate() {
    // 6 / 2 = 3
    assert_bv_eq(&sdiv_simulate(&[bv("0110"), bv("0010")]), "0011");
    // -6 / 2 = -3 (1010 / 0010 = 1101)
    assert_bv_eq(&sdiv_simulate(&[bv("1010"), bv("0010")]), "1101");
    // 6 / -2 = -3 (0110 / 1110 = 1101)
    assert_bv_eq(&sdiv_simulate(&[bv("0110"), bv("1110")]), "1101");
    // -6 / -2 = 3 (1010 / 1110 = 0011)
    assert_bv_eq(&sdiv_simulate(&[bv("1010"), bv("1110")]), "0011");
}

#[test]
fn test_srem_simulate() {
    // 7 % 3 = 1
    assert_bv_eq(&srem_simulate(&[bv("0111"), bv("0011")]), "0001");
    // -7 % 3 = -1 (1001 % 0011 = 1111)
    assert_bv_eq(&srem_simulate(&[bv("1001"), bv("0011")]), "1111");
    // 7 % -3 = 1 (0111 % 1101 = 0001)
    assert_bv_eq(&srem_simulate(&[bv("0111"), bv("1101")]), "0001");
    // -7 % -3 = -1 (1001 % 1101 = 1111)
    assert_bv_eq(&srem_simulate(&[bv("1001"), bv("1101")]), "1111");
}

#[test]
fn test_smod_simulate() {
    // 7 smod 3 = 1
    assert_bv_eq(&smod_simulate(&[bv("0111"), bv("0011")]), "0001");
    // -7 smod 3 = 2 (result has same sign as divisor)
    assert_bv_eq(&smod_simulate(&[bv("1001"), bv("0011")]), "0010");
    // 7 smod -3 = -2 (result has same sign as divisor)
    assert_bv_eq(&smod_simulate(&[bv("0111"), bv("1101")]), "1110");
    // -7 smod -3 = -1 (result has same sign as divisor)
    assert_bv_eq(&smod_simulate(&[bv("1001"), bv("1101")]), "1111");
}

#[test]
fn test_read_simulate() {
    // Array with 4 elements of 2 bits each: [00, 01, 10, 11]
    // Flat representation: 11_10_01_00
    let array = bv("11100100");
    // Read at index 0 -> 00
    assert_bv_eq(&read_simulate(&[array.clone(), bv("00")]), "00");
    // Read at index 1 -> 01
    assert_bv_eq(&read_simulate(&[array.clone(), bv("01")]), "01");
    // Read at index 2 -> 10
    assert_bv_eq(&read_simulate(&[array.clone(), bv("10")]), "10");
    // Read at index 3 -> 11
    assert_bv_eq(&read_simulate(&[array.clone(), bv("11")]), "11");
}

#[test]
fn test_write_simulate() {
    // Array with 4 elements of 2 bits each: [00, 01, 10, 11]
    // Flat representation: 11_10_01_00
    let array = bv("11100100");
    // Write 11 at index 0 -> [11, 01, 10, 11] = 11_10_01_11
    assert_bv_eq(
        &write_simulate(&[array.clone(), bv("00"), bv("11")]),
        "11100111",
    );
    // Write 00 at index 3 -> [00, 01, 10, 00] = 00_10_01_00
    assert_bv_eq(
        &write_simulate(&[array.clone(), bv("11"), bv("00")]),
        "00100100",
    );
    // Write 11 at index 1 -> [00, 11, 10, 11] = 11_10_11_00
    assert_bv_eq(
        &write_simulate(&[array.clone(), bv("01"), bv("11")]),
        "11101100",
    );
}
