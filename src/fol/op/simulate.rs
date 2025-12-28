use crate::fol::Value;
use crate::{Lbool, LboolVec};

pub fn not_simulate(terms: &[Value]) -> Value {
    let x = terms[0].as_bv().unwrap();
    Value::Bv(!x)
}

pub fn and_simulate(terms: &[Value]) -> Value {
    let x = terms[0].as_bv().unwrap();
    let y = terms[1].as_bv().unwrap();
    Value::Bv(x & y)
}

pub fn ands_simulate(terms: &[Value]) -> Value {
    let mut res = terms[0].as_bv().unwrap().clone();
    for t in &terms[1..] {
        res &= t.as_bv().unwrap();
    }
    Value::Bv(res)
}

pub fn or_simulate(terms: &[Value]) -> Value {
    let x = terms[0].as_bv().unwrap();
    let y = terms[1].as_bv().unwrap();
    Value::Bv(x | y)
}

pub fn ors_simulate(terms: &[Value]) -> Value {
    let mut res = terms[0].as_bv().unwrap().clone();
    for t in &terms[1..] {
        res |= t.as_bv().unwrap();
    }
    Value::Bv(res)
}

pub fn xor_simulate(terms: &[Value]) -> Value {
    let x = terms[0].as_bv().unwrap();
    let y = terms[1].as_bv().unwrap();
    Value::Bv(x ^ y)
}

pub fn eq_simulate(terms: &[Value]) -> Value {
    let x = terms[0].as_bv().unwrap();
    let y = terms[1].as_bv().unwrap();
    let xor_res = x ^ y;
    // Eq is true iff all bits are equal (xor is all zeros)
    let mut res = Lbool::TRUE;
    for bit in xor_res.iter() {
        if bit.is_none() {
            res = Lbool::NONE;
        } else if bit.is_true() {
            return Value::Bv(LboolVec::from_elem(Lbool::FALSE, 1));
        }
    }
    Value::Bv(LboolVec::from_elem(res, 1))
}

pub fn ult_simulate(terms: &[Value]) -> Value {
    let x = terms[0].as_bv().unwrap();
    let y = terms[1].as_bv().unwrap();
    // x < y unsigned
    let mut res = Lbool::FALSE;
    for (xb, yb) in x.iter().zip(y.iter()) {
        if xb.is_none() || yb.is_none() {
            res = Lbool::NONE;
        } else if !xb.is_true() && yb.is_true() {
            // !x & y => definitely less at this bit
            res = Lbool::TRUE;
        } else if xb.is_true() && !yb.is_true() {
            // x & !y => definitely greater at this bit
            res = Lbool::FALSE;
        }
        // else equal at this bit, keep previous result
    }
    Value::Bv(LboolVec::from_elem(res, 1))
}

pub fn slt_simulate(terms: &[Value]) -> Value {
    let x = terms[0].as_bv().unwrap();
    let y = terms[1].as_bv().unwrap();
    let len = x.len();
    let xs = x.get(len - 1); // sign bit of x
    let ys = y.get(len - 1); // sign bit of y

    if xs.is_none() || ys.is_none() {
        return Value::Bv(LboolVec::from_elem(Lbool::NONE, 1));
    }

    // If signs differ: x < y iff x is negative (xs=1, ys=0)
    if xs.is_true() && !ys.is_true() {
        return Value::Bv(LboolVec::from_elem(Lbool::TRUE, 1));
    }
    if !xs.is_true() && ys.is_true() {
        return Value::Bv(LboolVec::from_elem(Lbool::FALSE, 1));
    }

    // Same sign: compare as unsigned on the rest
    let mut res = Lbool::FALSE;
    for i in 0..len - 1 {
        let xb = x.get(i);
        let yb = y.get(i);
        if xb.is_none() || yb.is_none() {
            res = Lbool::NONE;
        } else if !xb.is_true() && yb.is_true() {
            res = Lbool::TRUE;
        } else if xb.is_true() && !yb.is_true() {
            res = Lbool::FALSE;
        }
    }
    Value::Bv(LboolVec::from_elem(res, 1))
}

pub fn sll_simulate(terms: &[Value]) -> Value {
    let x = terms[0].as_bv().unwrap();
    let y = terms[1].as_bv().unwrap();
    let width = x.len();

    // Convert shift amount to usize if possible
    let mut shift_amt: Option<usize> = Some(0);
    for (i, bit) in y.iter().enumerate() {
        if bit.is_none() {
            shift_amt = None;
            break;
        }
        if bit.is_true()
            && let Some(ref mut s) = shift_amt
        {
            *s |= 1 << i;
        }
    }

    match shift_amt {
        Some(s) if s >= width => Value::Bv(LboolVec::from_elem(Lbool::FALSE, width)),
        Some(s) => {
            let mut res = LboolVec::from_elem(Lbool::FALSE, width);
            for i in s..width {
                res.set(i, x.get(i - s));
            }
            Value::Bv(res)
        }
        None => Value::Bv(LboolVec::from_elem(Lbool::NONE, width)),
    }
}

pub fn srl_simulate(terms: &[Value]) -> Value {
    let x = terms[0].as_bv().unwrap();
    let y = terms[1].as_bv().unwrap();
    let width = x.len();

    let mut shift_amt: Option<usize> = Some(0);
    for (i, bit) in y.iter().enumerate() {
        if bit.is_none() {
            shift_amt = None;
            break;
        }
        if bit.is_true()
            && let Some(ref mut s) = shift_amt
        {
            *s |= 1 << i;
        }
    }

    match shift_amt {
        Some(s) if s >= width => Value::Bv(LboolVec::from_elem(Lbool::FALSE, width)),
        Some(s) => {
            let mut res = LboolVec::from_elem(Lbool::FALSE, width);
            for i in 0..width - s {
                res.set(i, x.get(i + s));
            }
            Value::Bv(res)
        }
        None => Value::Bv(LboolVec::from_elem(Lbool::NONE, width)),
    }
}

pub fn sra_simulate(terms: &[Value]) -> Value {
    let x = terms[0].as_bv().unwrap();
    let y = terms[1].as_bv().unwrap();
    let width = x.len();
    let sign = x.get(width - 1);

    let mut shift_amt: Option<usize> = Some(0);
    for (i, bit) in y.iter().enumerate() {
        if bit.is_none() {
            shift_amt = None;
            break;
        }
        if bit.is_true()
            && let Some(ref mut s) = shift_amt
        {
            *s |= 1 << i;
        }
    }

    match shift_amt {
        Some(s) if s >= width => Value::Bv(LboolVec::from_elem(sign, width)),
        Some(s) => {
            let mut res = LboolVec::from_elem(sign, width);
            for i in 0..width - s {
                res.set(i, x.get(i + s));
            }
            Value::Bv(res)
        }
        None => Value::Bv(LboolVec::from_elem(Lbool::NONE, width)),
    }
}

pub fn rol_simulate(terms: &[Value]) -> Value {
    let x = terms[0].as_bv().unwrap();
    let y = terms[1].as_bv().unwrap();
    let width = x.len();

    if width == 1 {
        return Value::Bv(x.clone());
    }

    let mut rot_amt: Option<usize> = Some(0);
    for (i, bit) in y.iter().enumerate() {
        if bit.is_none() {
            rot_amt = None;
            break;
        }
        if bit.is_true()
            && let Some(ref mut r) = rot_amt
        {
            *r |= 1 << i;
        }
    }

    match rot_amt {
        Some(r) => {
            let r = r % width;
            let mut res = LboolVec::from_elem(Lbool::NONE, width);
            for i in 0..width {
                res.set((i + r) % width, x.get(i));
            }
            Value::Bv(res)
        }
        None => Value::Bv(LboolVec::from_elem(Lbool::NONE, width)),
    }
}

pub fn ror_simulate(terms: &[Value]) -> Value {
    let x = terms[0].as_bv().unwrap();
    let y = terms[1].as_bv().unwrap();
    let width = x.len();

    if width == 1 {
        return Value::Bv(x.clone());
    }

    let mut rot_amt: Option<usize> = Some(0);
    for (i, bit) in y.iter().enumerate() {
        if bit.is_none() {
            rot_amt = None;
            break;
        }
        if bit.is_true()
            && let Some(ref mut r) = rot_amt
        {
            *r |= 1 << i;
        }
    }

    match rot_amt {
        Some(r) => {
            let r = r % width;
            let mut res = LboolVec::from_elem(Lbool::NONE, width);
            for i in 0..width {
                res.set(i, x.get((i + r) % width));
            }
            Value::Bv(res)
        }
        None => Value::Bv(LboolVec::from_elem(Lbool::NONE, width)),
    }
}

pub fn ite_simulate(terms: &[Value]) -> Value {
    let c = terms[0].as_bv().unwrap();
    let t = terms[1].as_bv().unwrap();
    let e = terms[2].as_bv().unwrap();

    let cond = c.get(0);
    if cond.is_none() {
        // If condition is unknown, result is unknown where t and e differ
        let mut res = LboolVec::from_elem(Lbool::NONE, t.len());
        for i in 0..t.len() {
            let tb = t.get(i);
            let eb = e.get(i);
            if !tb.is_none() && !eb.is_none() && tb == eb {
                res.set(i, tb);
            }
        }
        Value::Bv(res)
    } else if cond.is_true() {
        Value::Bv(t.clone())
    } else {
        Value::Bv(e.clone())
    }
}

pub fn concat_simulate(terms: &[Value]) -> Value {
    let x = terms[0].as_bv().unwrap(); // high bits
    let y = terms[1].as_bv().unwrap(); // low bits
    let mut res = LboolVec::from_elem(Lbool::NONE, x.len() + y.len());
    for i in 0..y.len() {
        res.set(i, y.get(i));
    }
    for i in 0..x.len() {
        res.set(y.len() + i, x.get(i));
    }
    Value::Bv(res)
}

pub fn sext_simulate(terms: &[Value]) -> Value {
    let x = terms[0].as_bv().unwrap();
    let ext = terms[1].as_bv().unwrap();
    let ext_len = ext.len();
    let sign = x.get(x.len() - 1);
    let mut res = LboolVec::from_elem(Lbool::NONE, x.len() + ext_len);
    for i in 0..x.len() {
        res.set(i, x.get(i));
    }
    for i in 0..ext_len {
        res.set(x.len() + i, sign);
    }
    Value::Bv(res)
}

pub fn slice_simulate(terms: &[Value]) -> Value {
    let s = terms[0].as_bv().unwrap();
    let h = terms[1].as_bv().unwrap().len(); // high index
    let l = terms[2].as_bv().unwrap().len(); // low index
    let mut res = LboolVec::from_elem(Lbool::NONE, h - l + 1);
    for i in l..=h {
        res.set(i - l, s.get(i));
    }
    Value::Bv(res)
}

pub fn redxor_simulate(terms: &[Value]) -> Value {
    let x = terms[0].as_bv().unwrap();
    let mut res = Lbool::FALSE;
    for bit in x.iter() {
        res = res ^ bit;
    }
    Value::Bv(LboolVec::from_elem(res, 1))
}

fn full_adder_sim(x: Lbool, y: Lbool, c: Lbool) -> (Lbool, Lbool) {
    let r = x ^ y ^ c;
    let co = (x & y) | (x & c) | (y & c);
    (r, co)
}

pub fn add_simulate(terms: &[Value]) -> Value {
    let x = terms[0].as_bv().unwrap();
    let y = terms[1].as_bv().unwrap();
    let mut res = LboolVec::from_elem(Lbool::NONE, x.len());
    let mut c = Lbool::FALSE;
    for i in 0..x.len() {
        let (r, nc) = full_adder_sim(x.get(i), y.get(i), c);
        res.set(i, r);
        c = nc;
    }
    Value::Bv(res)
}

pub fn sub_simulate(terms: &[Value]) -> Value {
    let x = terms[0].as_bv().unwrap();
    let y = terms[1].as_bv().unwrap();
    let mut res = LboolVec::from_elem(Lbool::NONE, x.len());
    let mut c = Lbool::TRUE;
    for i in 0..x.len() {
        let (r, nc) = full_adder_sim(x.get(i), !y.get(i), c);
        res.set(i, r);
        c = nc;
    }
    Value::Bv(res)
}

pub fn mul_simulate(terms: &[Value]) -> Value {
    let x = terms[0].as_bv().unwrap();
    let y = terms[1].as_bv().unwrap();
    let len = x.len();

    // Initialize result with x[i] & y[0]
    let mut res = LboolVec::from_elem(Lbool::NONE, len);
    for i in 0..len {
        res.set(i, x.get(i) & y.get(0));
    }

    for i in 1..len {
        let mut c = Lbool::FALSE;
        for j in i..len {
            let add = y.get(i) & x.get(j - i);
            let (r, nc) = full_adder_sim(res.get(j), add, c);
            res.set(j, r);
            c = nc;
        }
    }
    Value::Bv(res)
}

pub fn neg_simulate(terms: &[Value]) -> Value {
    let x = terms[0].as_bv().unwrap();
    let mut res = LboolVec::from_elem(Lbool::NONE, x.len());
    res.set(0, x.get(0));
    let mut c = !x.get(0);
    for i in 1..x.len() {
        let xi = x.get(i);
        res.set(i, (c & xi) | (!c & !xi));
        c = c & !xi;
    }
    Value::Bv(res)
}

pub fn udiv_simulate(terms: &[Value]) -> Value {
    let x = terms[0].as_bv().unwrap();
    let y = terms[1].as_bv().unwrap();
    let width = x.len();

    // Check if all bits are known
    let mut x_val: Option<u128> = Some(0);
    let mut y_val: Option<u128> = Some(0);

    for (i, bit) in x.iter().enumerate() {
        if bit.is_none() {
            x_val = None;
            break;
        }
        if bit.is_true()
            && let Some(ref mut v) = x_val
        {
            *v |= 1u128 << i;
        }
    }

    for (i, bit) in y.iter().enumerate() {
        if bit.is_none() {
            y_val = None;
            break;
        }
        if bit.is_true()
            && let Some(ref mut v) = y_val
        {
            *v |= 1u128 << i;
        }
    }

    match (x_val, y_val) {
        (Some(xv), Some(yv)) if yv != 0 => {
            let q = xv / yv;
            let mut res = LboolVec::from_elem(Lbool::FALSE, width);
            for i in 0..width {
                if (q >> i) & 1 == 1 {
                    res.set(i, Lbool::TRUE);
                }
            }
            Value::Bv(res)
        }
        _ => Value::Bv(LboolVec::from_elem(Lbool::NONE, width)),
    }
}

pub fn urem_simulate(terms: &[Value]) -> Value {
    let x = terms[0].as_bv().unwrap();
    let y = terms[1].as_bv().unwrap();
    let width = x.len();

    let mut x_val: Option<u128> = Some(0);
    let mut y_val: Option<u128> = Some(0);

    for (i, bit) in x.iter().enumerate() {
        if bit.is_none() {
            x_val = None;
            break;
        }
        if bit.is_true()
            && let Some(ref mut v) = x_val
        {
            *v |= 1u128 << i;
        }
    }

    for (i, bit) in y.iter().enumerate() {
        if bit.is_none() {
            y_val = None;
            break;
        }
        if bit.is_true()
            && let Some(ref mut v) = y_val
        {
            *v |= 1u128 << i;
        }
    }

    match (x_val, y_val) {
        (Some(xv), Some(yv)) if yv != 0 => {
            let r = xv % yv;
            let mut res = LboolVec::from_elem(Lbool::FALSE, width);
            for i in 0..width {
                if (r >> i) & 1 == 1 {
                    res.set(i, Lbool::TRUE);
                }
            }
            Value::Bv(res)
        }
        _ => Value::Bv(LboolVec::from_elem(Lbool::NONE, width)),
    }
}

pub fn sdiv_simulate(terms: &[Value]) -> Value {
    let x = terms[0].as_bv().unwrap();
    let y = terms[1].as_bv().unwrap();
    let width = x.len();

    let mut x_val: Option<i128> = Some(0);
    let mut y_val: Option<i128> = Some(0);

    for (i, bit) in x.iter().enumerate() {
        if bit.is_none() {
            x_val = None;
            break;
        }
        if bit.is_true()
            && let Some(ref mut v) = x_val
        {
            *v |= 1i128 << i;
        }
    }

    for (i, bit) in y.iter().enumerate() {
        if bit.is_none() {
            y_val = None;
            break;
        }
        if bit.is_true()
            && let Some(ref mut v) = y_val
        {
            *v |= 1i128 << i;
        }
    }

    // Sign extend
    if let Some(ref mut xv) = x_val
        && (*xv >> (width - 1)) & 1 == 1
    {
        *xv |= !((1i128 << width) - 1);
    }
    if let Some(ref mut yv) = y_val
        && (*yv >> (width - 1)) & 1 == 1
    {
        *yv |= !((1i128 << width) - 1);
    }

    match (x_val, y_val) {
        (Some(xv), Some(yv)) if yv != 0 => {
            let q = xv / yv;
            let mut res = LboolVec::from_elem(Lbool::FALSE, width);
            for i in 0..width {
                if (q >> i) & 1 == 1 {
                    res.set(i, Lbool::TRUE);
                }
            }
            Value::Bv(res)
        }
        _ => Value::Bv(LboolVec::from_elem(Lbool::NONE, width)),
    }
}

pub fn srem_simulate(terms: &[Value]) -> Value {
    let x = terms[0].as_bv().unwrap();
    let y = terms[1].as_bv().unwrap();
    let width = x.len();

    let mut x_val: Option<i128> = Some(0);
    let mut y_val: Option<i128> = Some(0);

    for (i, bit) in x.iter().enumerate() {
        if bit.is_none() {
            x_val = None;
            break;
        }
        if bit.is_true()
            && let Some(ref mut v) = x_val
        {
            *v |= 1i128 << i;
        }
    }

    for (i, bit) in y.iter().enumerate() {
        if bit.is_none() {
            y_val = None;
            break;
        }
        if bit.is_true()
            && let Some(ref mut v) = y_val
        {
            *v |= 1i128 << i;
        }
    }

    // Sign extend
    if let Some(ref mut xv) = x_val
        && (*xv >> (width - 1)) & 1 == 1
    {
        *xv |= !((1i128 << width) - 1);
    }
    if let Some(ref mut yv) = y_val
        && (*yv >> (width - 1)) & 1 == 1
    {
        *yv |= !((1i128 << width) - 1);
    }

    match (x_val, y_val) {
        (Some(xv), Some(yv)) if yv != 0 => {
            let r = xv % yv;
            let mut res = LboolVec::from_elem(Lbool::FALSE, width);
            for i in 0..width {
                if (r >> i) & 1 == 1 {
                    res.set(i, Lbool::TRUE);
                }
            }
            Value::Bv(res)
        }
        _ => Value::Bv(LboolVec::from_elem(Lbool::NONE, width)),
    }
}

pub fn smod_simulate(terms: &[Value]) -> Value {
    let x = terms[0].as_bv().unwrap();
    let y = terms[1].as_bv().unwrap();
    let width = x.len();

    let mut x_val: Option<i128> = Some(0);
    let mut y_val: Option<i128> = Some(0);

    for (i, bit) in x.iter().enumerate() {
        if bit.is_none() {
            x_val = None;
            break;
        }
        if bit.is_true()
            && let Some(ref mut v) = x_val
        {
            *v |= 1i128 << i;
        }
    }

    for (i, bit) in y.iter().enumerate() {
        if bit.is_none() {
            y_val = None;
            break;
        }
        if bit.is_true()
            && let Some(ref mut v) = y_val
        {
            *v |= 1i128 << i;
        }
    }

    // Sign extend
    if let Some(ref mut xv) = x_val
        && (*xv >> (width - 1)) & 1 == 1
    {
        *xv |= !((1i128 << width) - 1);
    }
    if let Some(ref mut yv) = y_val
        && (*yv >> (width - 1)) & 1 == 1
    {
        *yv |= !((1i128 << width) - 1);
    }

    match (x_val, y_val) {
        (Some(xv), Some(yv)) if yv != 0 => {
            // smod: result has same sign as divisor
            let mut r = xv % yv;
            if (r < 0 && yv > 0) || (r > 0 && yv < 0) {
                r += yv;
            }
            let mut res = LboolVec::from_elem(Lbool::FALSE, width);
            for i in 0..width {
                if (r >> i) & 1 == 1 {
                    res.set(i, Lbool::TRUE);
                }
            }
            Value::Bv(res)
        }
        _ => Value::Bv(LboolVec::from_elem(Lbool::NONE, width)),
    }
}

pub fn read_simulate(terms: &[Value]) -> Value {
    let array = terms[0].as_bv().unwrap();
    let index = terms[1].as_bv().unwrap();
    let index_len = index.len();
    let array_len = array.len();
    let index_range = 1usize << index_len;
    let element_len = array_len / index_range;

    // Convert index to usize if possible
    let mut idx_val: Option<usize> = Some(0);
    for (i, bit) in index.iter().enumerate() {
        if bit.is_none() {
            idx_val = None;
            break;
        }
        if bit.is_true()
            && let Some(ref mut v) = idx_val
        {
            *v |= 1 << i;
        }
    }

    match idx_val {
        Some(idx) => {
            let mut res = LboolVec::from_elem(Lbool::NONE, element_len);
            for i in 0..element_len {
                res.set(i, array.get(element_len * idx + i));
            }
            Value::Bv(res)
        }
        None => Value::Bv(LboolVec::from_elem(Lbool::NONE, element_len)),
    }
}

pub fn write_simulate(terms: &[Value]) -> Value {
    let array = terms[0].as_bv().unwrap();
    let index = terms[1].as_bv().unwrap();
    let value = terms[2].as_bv().unwrap();
    let index_len = index.len();
    let array_len = array.len();
    let index_range = 1usize << index_len;
    let element_len = array_len / index_range;

    // Convert index to usize if possible
    let mut idx_val: Option<usize> = Some(0);
    for (i, bit) in index.iter().enumerate() {
        if bit.is_none() {
            idx_val = None;
            break;
        }
        if bit.is_true()
            && let Some(ref mut v) = idx_val
        {
            *v |= 1 << i;
        }
    }

    match idx_val {
        Some(idx) => {
            let mut res = array.clone();
            for i in 0..element_len {
                res.set(element_len * idx + i, value.get(i));
            }
            Value::Bv(res)
        }
        None => {
            // If index is unknown, we don't know which element changes
            // Result is unknown for all elements
            Value::Bv(LboolVec::from_elem(Lbool::NONE, array_len))
        }
    }
}
