use crate::fol::{ArrayValue, FolOp, Value};
use crate::{Lbool, LboolVec};
use giputils::bitvec::BitVec;

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
    let array = terms[0].as_array().unwrap();
    let index = terms[1].as_bv().unwrap();
    let element_len = array.sort().array().1;
    if index.any_x() {
        return Value::Bv(LboolVec::from_elem(Lbool::NONE, element_len));
    }
    let index: BitVec = index.into();
    let index: usize = index.to_usize();
    Value::Bv(
        array
            .get(&index)
            .cloned()
            .unwrap_or_else(|| LboolVec::from_elem(Lbool::NONE, element_len)),
    )
}

pub fn write_simulate(terms: &[Value]) -> Value {
    let array = terms[0].as_array().unwrap();
    let index = terms[1].as_bv().unwrap();
    if index.any_x() {
        return Value::Array(ArrayValue::default_from(array.sort()));
    }
    let index: BitVec = index.into();
    let index: usize = index.to_usize();
    let value = terms[2].as_bv().unwrap();
    let mut res = array.clone();
    res.insert(index, value.clone());
    Value::Array(res)
}

impl FolOp {
    pub fn simulate(&self, vals: &[Value]) -> Value {
        match self {
            FolOp::Not => not_simulate(vals),
            FolOp::And => and_simulate(vals),
            FolOp::Ands => ands_simulate(vals),
            FolOp::Or => or_simulate(vals),
            FolOp::Ors => ors_simulate(vals),
            FolOp::Xor => xor_simulate(vals),
            FolOp::Eq => eq_simulate(vals),
            FolOp::Ult => ult_simulate(vals),
            FolOp::Slt => slt_simulate(vals),
            FolOp::Sll => sll_simulate(vals),
            FolOp::Srl => srl_simulate(vals),
            FolOp::Sra => sra_simulate(vals),
            FolOp::Rol => rol_simulate(vals),
            FolOp::Ror => ror_simulate(vals),
            FolOp::Ite => ite_simulate(vals),
            FolOp::Concat => concat_simulate(vals),
            FolOp::Sext => sext_simulate(vals),
            FolOp::Slice => slice_simulate(vals),
            FolOp::Redxor => redxor_simulate(vals),
            FolOp::Add => add_simulate(vals),
            FolOp::Sub => sub_simulate(vals),
            FolOp::Mul => mul_simulate(vals),
            FolOp::Udiv => udiv_simulate(vals),
            FolOp::Urem => urem_simulate(vals),
            FolOp::Neg => neg_simulate(vals),
            FolOp::Sdiv => sdiv_simulate(vals),
            FolOp::Srem => srem_simulate(vals),
            FolOp::Smod => smod_simulate(vals),
            FolOp::Read => read_simulate(vals),
            FolOp::Write => write_simulate(vals),
            _ => panic!("{:?} not support simulate", self),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::LboolVec;
    use crate::fol::{Sort, Value};

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
        let mut array = ArrayValue::default_from(Sort::Array(2, 2));
        array.insert(0, LboolVec::from("00"));
        array.insert(1, LboolVec::from("01"));
        array.insert(2, LboolVec::from("10"));
        array.insert(3, LboolVec::from("11"));
        let array = Value::Array(array);
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
        let mut array = ArrayValue::default_from(Sort::Array(2, 2));
        array.insert(0, LboolVec::from("00"));
        array.insert(1, LboolVec::from("01"));
        array.insert(2, LboolVec::from("10"));
        array.insert(3, LboolVec::from("11"));
        let array = Value::Array(array);

        let written = write_simulate(&[array.clone(), bv("00"), bv("11")]);
        assert_bv_eq(&read_simulate(&[written, bv("00")]), "11");

        let written = write_simulate(&[array.clone(), bv("11"), bv("00")]);
        assert_bv_eq(&read_simulate(&[written, bv("11")]), "00");

        let written = write_simulate(&[array, bv("01"), bv("11")]);
        assert_bv_eq(&read_simulate(&[written, bv("01")]), "11");
    }

    #[test]
    fn test_sparse_array_read_write_simulate() {
        let mut array = ArrayValue::default_from(Sort::Array(2, 2));
        array.insert(1, LboolVec::from("01"));
        array.insert(3, LboolVec::from("11"));
        let array = Value::Array(array);

        assert_bv_eq(&read_simulate(&[array.clone(), bv("01")]), "01");
        assert_bv_eq(&read_simulate(&[array.clone(), bv("00")]), "xx");
        assert_bv_eq(&read_simulate(&[array.clone(), bv("0x")]), "xx");

        let written = write_simulate(&[array, bv("10"), bv("10")]);
        assert_bv_eq(&read_simulate(&[written, bv("10")]), "10");
    }
}
