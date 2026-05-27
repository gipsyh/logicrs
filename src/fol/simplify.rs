use super::Term;
use crate::fol::TermResult;
use crate::fol::Value;
use crate::fol::op::*;
use giputils::bitvec::BitVec;
use giputils::hash::GHashMap;

/// Compiler-style optimization level used by simplification/canonicalization.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OptLevel {
    O0 = 0,
    O1 = 1,
    O2 = 2,
    O3 = 3,
}

impl Default for OptLevel {
    #[inline]
    fn default() -> Self {
        Self::O2
    }
}

impl OptLevel {
    #[inline]
    pub const fn at_least(self, other: OptLevel) -> bool {
        self as u8 >= other as u8
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SimplifyCtx {
    pub level: OptLevel,
}

impl Default for SimplifyCtx {
    #[inline]
    fn default() -> Self {
        Self {
            level: OptLevel::default(),
        }
    }
}

impl SimplifyCtx {
    #[inline]
    pub const fn new(level: OptLevel) -> Self {
        Self { level }
    }
}

trait RewriteRule {
    #[inline]
    fn opt_level(&self) -> OptLevel {
        OptLevel::O1
    }

    fn apply(&self, terms: &[Term]) -> TermResult;
}

struct RewritePipeline {
    level: OptLevel,
    rules: Vec<Box<dyn RewriteRule>>,
}

impl RewritePipeline {
    fn new(level: OptLevel) -> Self {
        Self {
            level,
            rules: Vec::new(),
        }
    }

    fn with_rule(mut self, rule: impl RewriteRule + 'static) -> Self {
        self.rules.push(Box::new(rule));
        self
    }
}

impl RewriteRule for RewritePipeline {
    fn opt_level(&self) -> OptLevel {
        self.level
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        for rule in self.rules.iter() {
            if !self.level.at_least(rule.opt_level()) {
                continue;
            }
            if let Some(res) = rule.apply(terms) {
                return Some(res);
            }
        }
        None
    }
}

fn msb_bit_term(term: &Term) -> Option<Term> {
    if term.bv_len() == 1 {
        return Some(term.clone());
    }
    let op = term.try_op()?;
    if op.op == Concat || op.op == Sext {
        msb_bit_term(&op[0])
    } else {
        None
    }
}

fn collect_assoc_terms(op: FolOp, term: &Term, out: &mut Vec<Term>) {
    if let Some(top) = term.try_op()
        && top.op == op
    {
        collect_assoc_terms(op, &top[0], out);
        collect_assoc_terms(op, &top[1], out);
        return;
    }
    out.push(term.clone());
}

fn slice_bit_literal(term: &Term) -> Option<(Term, usize, bool)> {
    let (inner, positive) = if let Some(top) = term.try_op()
        && top.op == Not
    {
        (&top[0], false)
    } else {
        (term, true)
    };

    let op = inner.try_op()?;
    if op.op != Slice {
        return None;
    }
    let base = op[0].clone();
    let h = op[1].bv_len();
    let l = op[2].bv_len();
    if h != l {
        return None;
    }
    Some((base, h, positive))
}

fn eq_slice_const(term: &Term) -> Option<(Term, usize, usize, Term)> {
    let op = term.try_op()?;
    if op.op != Eq {
        return None;
    }

    let (slice, cst) = if op[0].try_bv_const().is_some() {
        (&op[1], &op[0])
    } else if op[1].try_bv_const().is_some() {
        (&op[0], &op[1])
    } else {
        return None;
    };

    let sop = slice.try_op()?;
    if sop.op != Slice {
        return None;
    }
    let base = sop[0].clone();
    let h = sop[1].bv_len();
    let l = sop[2].bv_len();
    if h < l {
        return None;
    }
    Some((base, l, h, cst.clone()))
}

fn eq_term_const(term: &Term) -> Option<(Term, BitVec)> {
    let op = term.try_op()?;
    if op.op != Eq {
        return None;
    }

    if let Some(c) = op[0].try_bv_const() {
        return Some((op[1].clone(), c.clone()));
    }
    if let Some(c) = op[1].try_bv_const() {
        return Some((op[0].clone(), c.clone()));
    }
    None
}

fn single_bit_diff_idx(a: &BitVec, b: &BitVec) -> Option<usize> {
    if a.len() != b.len() {
        return None;
    }
    let mut diff_idx: Option<usize> = None;
    for (idx, (b1, b2)) in a.iter().zip(b.iter()).enumerate() {
        if b1 != b2 {
            if diff_idx.is_some() {
                return None;
            }
            diff_idx = Some(idx);
        }
    }
    diff_idx
}

fn or_eq_term_consts_one_bit_diff(x: &Term, c1: &BitVec, c2: &BitVec) -> Option<Term> {
    let w = c1.len();
    if w == 0 || w != c2.len() || x.bv_len() != w {
        return None;
    }

    let diff_idx = single_bit_diff_idx(c1, c2)?;
    if w == 1 {
        // (x == 0) | (x == 1) is a tautology.
        return Some(Term::bool_const(true));
    }

    // If the differing bit is at an edge, prefer a slice-based rewrite (no mask const).
    if diff_idx == 0 {
        let slice = x.slice(1, w - 1);
        let mut c = BitVec::zero(w - 1);
        for (idx, bit) in c1.iter().enumerate().skip(1) {
            c.set(idx - 1, bit);
        }
        return Some(slice.op1(Eq, Term::bv_const(c)));
    }
    if diff_idx == w - 1 {
        let slice = x.slice(0, w - 2);
        let mut c = BitVec::zero(w - 1);
        for (idx, bit) in c1.iter().enumerate().take(w - 1) {
            c.set(idx, bit);
        }
        return Some(slice.op1(Eq, Term::bv_const(c)));
    }

    // General case: mask out the differing bit.
    let mut mask = BitVec::ones(w);
    mask.set(diff_idx, false);
    let mask = Term::bv_const(mask);
    let masked = x & &mask;

    let mut c = c1.clone();
    c.set(diff_idx, false);
    let c = Term::bv_const(c);
    Some(masked.op1(Eq, &c))
}

struct NotXorBoolToEq;
impl RewriteRule for NotXorBoolToEq {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        if !x.is_bool() {
            return None;
        }
        let xop = x.try_op()?;
        if xop.op != Xor {
            return None;
        }
        Some(xop[0].op1(Eq, &xop[1]))
    }
}

pub(crate) fn not_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    let pipeline = RewritePipeline::new(ctx.level).with_rule(NotXorBoolToEq);
    pipeline.apply(terms)
}

struct AndConstPropagation;
impl RewriteRule for AndConstPropagation {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        if let Some(ac) = a.try_bv_const() {
            if ac.is_ones() {
                return Some(b.clone());
            }
            if ac.is_zero() {
                return Some(a.clone());
            }
        }
        None
    }
}

struct AndComplement;
impl RewriteRule for AndComplement {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        if a == !b {
            return Some(a.mk_bv_const_zero());
        }
        None
    }
}

struct AndMergeNestedAnds;
impl RewriteRule for AndMergeNestedAnds {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        let aop = a.try_op()?;
        if aop.op != And {
            return None;
        }
        if b == aop[0] {
            return Some(b & &aop[1]);
        }
        if b == aop[1] {
            return Some(b & &aop[0]);
        }
        let bop = b.try_op()?;
        if bop.op == And {
            if aop[0] == bop[0] {
                return Some(&aop[0] & &aop[1] & &bop[1]);
            }
            if aop[0] == bop[1] {
                return Some(&aop[0] & &aop[1] & &bop[0]);
            }
            if aop[1] == bop[0] {
                return Some(&aop[1] & &aop[0] & &bop[1]);
            }
            if aop[1] == bop[1] {
                return Some(&aop[1] & &aop[0] & &bop[0]);
            }
        }
        None
    }
}

struct AndDeMorganNotNot;
impl RewriteRule for AndDeMorganNotNot {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        let aop = a.try_op()?;
        if aop.op == Not
            && let Some(bop) = b.try_op()
            && bop.op == Not
        {
            return Some(!(&aop[0] | &bop[0]));
        }
        None
    }
}

struct AndAbsorbComplementInOr;
impl RewriteRule for AndAbsorbComplementInOr {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        let bop = b.try_op()?;
        if bop.op != Or {
            return None;
        }

        let not_a = !a.clone();
        if bop[0] == not_a {
            return Some(a & &bop[1]);
        }
        if bop[1] == not_a {
            return Some(a & &bop[0]);
        }

        if a == !&bop[0] {
            return Some(a & &bop[1]);
        }
        if a == !&bop[1] {
            return Some(a & &bop[0]);
        }
        None
    }
}

struct AndDistributeOverOr;
impl RewriteRule for AndDistributeOverOr {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        let aop = a.try_op()?;
        if aop.op != Or {
            return None;
        }

        if aop[0] == *b || aop[1] == *b {
            return Some(b.clone());
        }

        let bop = b.try_op()?;
        if bop.op == Or {
            if aop[0] == bop[0] {
                return Some(&aop[0] | (&aop[1] & &bop[1]));
            }
            if aop[0] == bop[1] {
                return Some(&aop[0] | (&aop[1] & &bop[0]));
            }
            if aop[1] == bop[0] {
                return Some(&aop[1] | (&aop[0] & &bop[1]));
            }
            if aop[1] == bop[1] {
                return Some(&aop[1] | (&aop[0] & &bop[0]));
            }
        }
        None
    }
}

struct AndMergeAdjacentEqSliceConsts;
impl RewriteRule for AndMergeAdjacentEqSliceConsts {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];

        // eq(slice(x, l1..h1), c1) & eq(slice(x, l2..h2), c2)
        //  => eq(slice(x, min(l1,l2)..max(h1,h2)), concat(c_hi, c_lo))
        if a.is_bool()
            && let (Some((base1, l1, h1, c1)), Some((base2, l2, h2, c2))) =
                (eq_slice_const(a), eq_slice_const(b))
            && base1 == base2
        {
            if h1 + 1 == l2 {
                let rhs = Term::new_op(Concat, [c2.clone(), c1.clone()]);
                return Some(base1.slice(l1, h2).op1(Eq, &rhs));
            }
            if h2 + 1 == l1 {
                let rhs = Term::new_op(Concat, [c1.clone(), c2.clone()]);
                return Some(base1.slice(l2, h1).op1(Eq, &rhs));
            }
        }
        None
    }
}

struct AndBitLevelEqReconstruction;
impl RewriteRule for AndBitLevelEqReconstruction {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];

        // (x[i] & ... & x[j]) == <const> (bit-level equality reconstruction)
        if !a.is_bool() {
            return None;
        }
        let mut leaves = Vec::new();
        collect_assoc_terms(FolOp::And, a, &mut leaves);
        collect_assoc_terms(FolOp::And, b, &mut leaves);

        let mut base: Option<Term> = None;
        let mut bits_by_idx = std::collections::BTreeMap::<usize, bool>::new();
        for leaf in leaves.iter() {
            let (b, idx, bit_is_one) = slice_bit_literal(leaf)?;
            if let Some(ref bb) = base {
                if *bb != b {
                    return None;
                }
            } else {
                base = Some(b);
            }
            if let Some(prev) = bits_by_idx.insert(idx, bit_is_one)
                && prev != bit_is_one
            {
                return Some(a.mk_bv_const_zero());
            }
        }
        let base = base?;
        let (lo, _) = bits_by_idx.first_key_value()?;
        let (hi, _) = bits_by_idx.last_key_value()?;
        let (lo, hi) = (*lo, *hi);
        if bits_by_idx.len() == hi - lo + 1 {
            let slice = base.slice(lo, hi);
            let mut rhs = BitVec::zero(hi - lo + 1);
            for (idx, bit_is_one) in bits_by_idx.iter() {
                rhs.set(idx - lo, *bit_is_one);
            }
            let rhs = Term::bv_const(rhs);
            return Some(slice.op1(Eq, &rhs));
        }
        None
    }
}

struct AndBitLevelMaskedEqReconstruction;
impl RewriteRule for AndBitLevelMaskedEqReconstruction {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O2
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];

        // (x[i]=c1) & (x[j]=c2) & ...  =>  ((slice(x, lo..hi) & mask) == rhs)
        // Works even when indices are not contiguous (mask has zeros for gaps).
        if !a.is_bool() {
            return None;
        }

        let mut leaves = Vec::new();
        collect_assoc_terms(FolOp::And, a, &mut leaves);
        collect_assoc_terms(FolOp::And, b, &mut leaves);

        let mut base: Option<Term> = None;
        let mut bits_by_idx = std::collections::BTreeMap::<usize, bool>::new();
        for leaf in leaves.iter() {
            let (b, idx, bit_is_one) = slice_bit_literal(leaf)?;
            if let Some(ref bb) = base {
                if *bb != b {
                    return None;
                }
            } else {
                base = Some(b);
            }
            if let Some(prev) = bits_by_idx.insert(idx, bit_is_one)
                && prev != bit_is_one
            {
                return Some(a.mk_bv_const_zero());
            }
        }

        // Heuristic: only rewrite when there are enough constrained bits to offset
        // the extra mask/eq/slice nodes this introduces.
        if bits_by_idx.len() < 8 {
            return None;
        }

        let base = base?;
        let (lo, _) = bits_by_idx.first_key_value()?;
        let (hi, _) = bits_by_idx.last_key_value()?;
        let (lo, hi) = (*lo, *hi);
        let w = hi - lo + 1;

        let slice = base.slice(lo, hi);
        let mut mask = BitVec::zero(w);
        let mut rhs = BitVec::zero(w);
        for (idx, bit_is_one) in bits_by_idx.iter() {
            let pos = idx - lo;
            mask.set(pos, true);
            rhs.set(pos, *bit_is_one);
        }
        let rhs = Term::bv_const(rhs);

        if mask.is_ones() {
            return Some(slice.op1(Eq, &rhs));
        }

        let mask = Term::bv_const(mask);
        let masked = &slice & &mask;
        Some(masked.op1(Eq, &rhs))
    }
}

pub(crate) fn and_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    let pipeline = RewritePipeline::new(ctx.level)
        .with_rule(AndConstPropagation)
        .with_rule(AndComplement)
        .with_rule(AndMergeNestedAnds)
        .with_rule(AndDeMorganNotNot)
        .with_rule(AndAbsorbComplementInOr)
        .with_rule(AndDistributeOverOr)
        .with_rule(AndMergeAdjacentEqSliceConsts)
        .with_rule(AndBitLevelEqReconstruction)
        .with_rule(AndBitLevelMaskedEqReconstruction);
    pipeline.apply(terms)
}

struct OrConstPropagation;
impl RewriteRule for OrConstPropagation {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        if let Some(ac) = a.try_bv_const() {
            if ac.is_ones() {
                return Some(a.clone());
            }
            if ac.is_zero() {
                return Some(b.clone());
            }
        }
        None
    }
}

struct OrComplement;
impl RewriteRule for OrComplement {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        if a == !b {
            return Some(a.mk_bv_const_ones());
        }
        None
    }
}

struct OrMergeNestedOrs;
impl RewriteRule for OrMergeNestedOrs {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        let aop = a.try_op()?;
        if aop.op != Or {
            return None;
        }
        if b == aop[0] {
            return Some(b | &aop[1]);
        }
        if b == aop[1] {
            return Some(b | &aop[0]);
        }
        let bop = b.try_op()?;
        if bop.op == Or {
            if aop[0] == bop[0] {
                return Some(&aop[0] | &aop[1] | &bop[1]);
            }
            if aop[0] == bop[1] {
                return Some(&aop[0] | &aop[1] | &bop[0]);
            }
            if aop[1] == bop[0] {
                return Some(&aop[1] | &aop[0] | &bop[1]);
            }
            if aop[1] == bop[1] {
                return Some(&aop[1] | &aop[0] | &bop[0]);
            }
        }
        None
    }
}

struct OrDeMorganNotNot;
impl RewriteRule for OrDeMorganNotNot {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        let aop = a.try_op()?;
        if aop.op == Not
            && let Some(bop) = b.try_op()
            && bop.op == Not
        {
            return Some(!(&aop[0] & &bop[0]));
        }
        None
    }
}

struct OrAbsorbComplementInAnd;
impl RewriteRule for OrAbsorbComplementInAnd {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        let bop = b.try_op()?;
        if bop.op != And {
            return None;
        }

        let not_a = !a.clone();
        if bop[0] == not_a {
            return Some(a | &bop[1]);
        }
        if bop[1] == not_a {
            return Some(a | &bop[0]);
        }

        if a == !&bop[0] {
            return Some(a | &bop[1]);
        }
        if a == !&bop[1] {
            return Some(a | &bop[0]);
        }
        None
    }
}

struct OrAbsorbIteCond;
impl RewriteRule for OrAbsorbIteCond {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        let aop = a.try_op()?;
        if aop.op != Ite {
            return None;
        }
        if b == aop[0] {
            return Some(b | &aop[2]);
        }
        if b == !&aop[0] {
            return Some(b | &aop[1]);
        }
        None
    }
}

struct OrDistributeOverAnd;
impl RewriteRule for OrDistributeOverAnd {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        let aop = a.try_op()?;
        if aop.op != And {
            return None;
        }

        if aop[0] == *b || aop[1] == *b {
            return Some(b.clone());
        }

        let bop = b.try_op()?;
        if bop.op == And {
            if aop[0] == bop[0] {
                return Some(&aop[0] & (&aop[1] | &bop[1]));
            }
            if aop[0] == bop[1] {
                return Some(&aop[0] & (&aop[1] | &bop[0]));
            }
            if aop[1] == bop[0] {
                return Some(&aop[1] & (&aop[0] | &bop[1]));
            }
            if aop[1] == bop[1] {
                return Some(&aop[1] & (&aop[0] | &bop[0]));
            }
        }
        None
    }
}

struct OrMergeEqConstOneBitDiff;
impl RewriteRule for OrMergeEqConstOneBitDiff {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];

        // (x == c1) | (x == c2) where c1,c2 differ by exactly one bit.
        let (x, c1) = eq_term_const(a)?;
        let (y, c2) = eq_term_const(b)?;
        if x != y {
            return None;
        }
        or_eq_term_consts_one_bit_diff(&x, &c1, &c2)
    }
}

struct OrMergeEqConstOneBitDiffAssoc;
impl RewriteRule for OrMergeEqConstOneBitDiffAssoc {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O2
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        if !a.is_bool() {
            return None;
        }

        let mut leaves = Vec::new();
        collect_assoc_terms(FolOp::Or, a, &mut leaves);
        collect_assoc_terms(FolOp::Or, b, &mut leaves);
        if leaves.len() <= 2 {
            return None;
        }

        let mut seen = GHashMap::<Term, Vec<(usize, BitVec)>>::new();
        for (idx, leaf) in leaves.iter().enumerate() {
            let Some((t, c)) = eq_term_const(leaf) else {
                continue;
            };

            if let Some(prevs) = seen.get(&t) {
                for (prev_idx, prev_c) in prevs.iter() {
                    if let Some(merged) = or_eq_term_consts_one_bit_diff(&t, prev_c, &c) {
                        let (i, j) = if *prev_idx < idx {
                            (*prev_idx, idx)
                        } else {
                            (idx, *prev_idx)
                        };
                        let mut new_leaves = Vec::with_capacity(leaves.len() - 1);
                        for (k, leaf) in leaves.iter().enumerate() {
                            if k == i {
                                new_leaves.push(merged.clone());
                            } else if k == j {
                                continue;
                            } else {
                                new_leaves.push(leaf.clone());
                            }
                        }

                        let mut acc = new_leaves[0].clone();
                        for leaf in new_leaves.iter().skip(1) {
                            acc = &acc | leaf;
                        }
                        return Some(acc);
                    }
                }
            }

            seen.entry(t).or_default().push((idx, c));
        }

        None
    }
}

struct OrBitLevelClauseReconstruction;
impl RewriteRule for OrBitLevelClauseReconstruction {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];

        // (x[i] | ... | x[j]) != <const> (bit-level clause reconstruction)
        if !a.is_bool() {
            return None;
        }
        let mut leaves = Vec::new();
        collect_assoc_terms(FolOp::Or, a, &mut leaves);
        collect_assoc_terms(FolOp::Or, b, &mut leaves);

        let mut base: Option<Term> = None;
        let mut pol_by_idx = std::collections::BTreeMap::<usize, bool>::new();
        for leaf in leaves.iter() {
            let (b, idx, positive) = slice_bit_literal(leaf)?;
            if let Some(ref bb) = base {
                if *bb != b {
                    return None;
                }
            } else {
                base = Some(b);
            }
            if let Some(prev) = pol_by_idx.insert(idx, positive)
                && prev != positive
            {
                return Some(a.mk_bv_const_ones());
            }
        }
        let base = base?;
        let (lo, _) = pol_by_idx.first_key_value()?;
        let (hi, _) = pol_by_idx.last_key_value()?;
        let (lo, hi) = (*lo, *hi);
        if pol_by_idx.len() == hi - lo + 1 {
            let slice = base.slice(lo, hi);
            // a clause is false only if every literal is false
            let mut rhs = BitVec::zero(hi - lo + 1);
            for (idx, positive) in pol_by_idx.iter() {
                rhs.set(idx - lo, !positive);
            }
            let rhs = Term::bv_const(rhs);
            return Some(!slice.op1(Eq, &rhs));
        }
        None
    }
}

struct OrBitLevelMaskedClauseReconstruction;
impl RewriteRule for OrBitLevelMaskedClauseReconstruction {
    fn opt_level(&self) -> OptLevel {
        OptLevel::O2
    }

    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];

        // (x[i] | ... | x[j]) != <const> (bit-level clause reconstruction with gaps)
        // (x[i]=p1) | (x[j]=p2) | ...  =>  !((slice(x, lo..hi) & mask) == rhs)
        // where rhs encodes the unique assignment that falsifies every literal.
        if !a.is_bool() {
            return None;
        }

        let mut leaves = Vec::new();
        collect_assoc_terms(FolOp::Or, a, &mut leaves);
        collect_assoc_terms(FolOp::Or, b, &mut leaves);

        let mut base: Option<Term> = None;
        let mut pol_by_idx = std::collections::BTreeMap::<usize, bool>::new();
        for leaf in leaves.iter() {
            let (b, idx, positive) = slice_bit_literal(leaf)?;
            if let Some(ref bb) = base {
                if *bb != b {
                    return None;
                }
            } else {
                base = Some(b);
            }
            if let Some(prev) = pol_by_idx.insert(idx, positive)
                && prev != positive
            {
                return Some(a.mk_bv_const_ones());
            }
        }

        // Heuristic: only rewrite when there are enough constrained bits to offset
        // the extra mask/eq/slice nodes this introduces.
        if pol_by_idx.len() < 8 {
            return None;
        }

        let base = base?;
        let (lo, _) = pol_by_idx.first_key_value()?;
        let (hi, _) = pol_by_idx.last_key_value()?;
        let (lo, hi) = (*lo, *hi);
        let w = hi - lo + 1;

        let slice = base.slice(lo, hi);
        let mut mask = BitVec::zero(w);
        let mut rhs = BitVec::zero(w);
        for (idx, positive) in pol_by_idx.iter() {
            let pos = idx - lo;
            mask.set(pos, true);
            rhs.set(pos, !positive);
        }
        let rhs = Term::bv_const(rhs);

        if mask.is_ones() {
            return Some(!slice.op1(Eq, &rhs));
        }

        let mask = Term::bv_const(mask);
        let masked = &slice & &mask;
        Some(!masked.op1(Eq, &rhs))
    }
}

pub(crate) fn or_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    let pipeline = RewritePipeline::new(ctx.level)
        .with_rule(OrConstPropagation)
        .with_rule(OrComplement)
        .with_rule(OrMergeNestedOrs)
        .with_rule(OrDeMorganNotNot)
        .with_rule(OrAbsorbComplementInAnd)
        .with_rule(OrDistributeOverAnd)
        .with_rule(OrAbsorbIteCond)
        .with_rule(OrMergeEqConstOneBitDiff)
        .with_rule(OrMergeEqConstOneBitDiffAssoc)
        .with_rule(OrBitLevelClauseReconstruction)
        .with_rule(OrBitLevelMaskedClauseReconstruction);
    pipeline.apply(terms)
}

struct XorConstPropagation;
impl RewriteRule for XorConstPropagation {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        if let Some(ac) = a.try_bv_const() {
            if ac.is_ones() {
                return Some(!b.clone());
            }
            if ac.is_zero() {
                return Some(b.clone());
            }
        }
        None
    }
}

struct XorSelf;
impl RewriteRule for XorSelf {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        if a == b {
            return Some(a.mk_bv_const_zero());
        }
        None
    }
}

struct XorComplement;
impl RewriteRule for XorComplement {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let a = &terms[0];
        let b = &terms[1];
        if a == !b {
            return Some(a.mk_bv_const_ones());
        }
        None
    }
}

pub(crate) fn xor_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    let pipeline = RewritePipeline::new(ctx.level)
        .with_rule(XorConstPropagation)
        .with_rule(XorSelf)
        .with_rule(XorComplement);
    pipeline.apply(terms)
}

struct EqBoolViaXor;
impl RewriteRule for EqBoolViaXor {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];
        if !x.is_bool() {
            return None;
        }

        // eq(x,y) = !xor(x,y), reusing (a subset of) xor simplifications without needing ctx.
        let xor_simplified = if let Some(xc) = x.try_bv_const() {
            if xc.is_ones() {
                Some(!y.clone())
            } else if xc.is_zero() {
                Some(y.clone())
            } else {
                None
            }
        } else if x == y {
            Some(x.mk_bv_const_zero())
        } else if x == !y {
            Some(x.mk_bv_const_ones())
        } else {
            None
        }?;
        Some(!xor_simplified)
    }
}

struct EqRefl;
impl RewriteRule for EqRefl {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];
        if x == y {
            return Some(Term::bool_const(true));
        }
        None
    }
}

struct EqComplement;
impl RewriteRule for EqComplement {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];
        if x == !y {
            return Some(Term::bool_const(false));
        }
        None
    }
}

struct EqNotConst;
impl RewriteRule for EqNotConst {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];

        // eq(!x, !y) => eq(x, y)
        if let Some(xop) = x.try_op()
            && xop.op == Not
            && let Some(yop) = y.try_op()
            && yop.op == Not
        {
            return Some(xop[0].op1(Eq, &yop[0]));
        }

        // eq(!x, c) => eq(x, !c) (push Not into constant)
        if let Some(yc) = y.try_bv_const()
            && let Some(xop) = x.try_op()
            && xop.op == Not
        {
            let mut nc = BitVec::zero(yc.len());
            for (idx, bit) in yc.iter().enumerate() {
                nc.set(idx, !bit);
            }
            return Some(xop[0].op1(Eq, Term::bv_const(nc)));
        }

        // eq(c, !x) => eq(x, !c) (symmetry)
        if let Some(xc) = x.try_bv_const()
            && let Some(yop) = y.try_op()
            && yop.op == Not
        {
            let mut nc = BitVec::zero(xc.len());
            for (idx, bit) in xc.iter().enumerate() {
                nc.set(idx, !bit);
            }
            return Some(yop[0].op1(Eq, Term::bv_const(nc)));
        }

        None
    }
}

struct EqXorZero;
impl RewriteRule for EqXorZero {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];

        // eq(xor(a,b), 0) => eq(a,b)
        let (xor_term, cst) = if let Some(xc) = x.try_bv_const() {
            (y, xc)
        } else if let Some(yc) = y.try_bv_const() {
            (x, yc)
        } else {
            return None;
        };
        if !cst.is_zero() {
            return None;
        }
        let xop = xor_term.try_op()?;
        if xop.op != Xor {
            return None;
        }
        Some(xop[0].op1(Eq, &xop[1]))
    }
}

pub(crate) fn eq_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    let pipeline = RewritePipeline::new(ctx.level)
        .with_rule(EqBoolViaXor)
        .with_rule(EqRefl)
        .with_rule(EqComplement)
        .with_rule(EqNotConst)
        .with_rule(EqXorZero);
    pipeline.apply(terms)
}

struct UltConstX;
impl RewriteRule for UltConstX {
    fn apply(&self, terms: &[Term]) -> TermResult {
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
        None
    }
}

struct UltConstY;
impl RewriteRule for UltConstY {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];
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
}

pub(crate) fn ult_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    let pipeline = RewritePipeline::new(ctx.level)
        .with_rule(UltConstX)
        .with_rule(UltConstY);
    pipeline.apply(terms)
}

struct IteConstCond;
impl RewriteRule for IteConstCond {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let (c, t, e) = (&terms[0], &terms[1], &terms[2]);
        let cc = c.try_bv_const()?;
        if cc.is_ones() {
            return Some(t.clone());
        }
        Some(e.clone())
    }
}

struct IteSameBranches;
impl RewriteRule for IteSameBranches {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let t = &terms[1];
        let e = &terms[2];
        if t == e {
            return Some(t.clone());
        }
        None
    }
}

struct IteNotCondSwap;
impl RewriteRule for IteNotCondSwap {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let (c, t, e) = (&terms[0], &terms[1], &terms[2]);
        let cop = c.try_op()?;
        if cop.op == Not {
            return Some(cop[0].ite(e, t));
        }
        None
    }
}

struct IteBoolComplementBranches;
impl RewriteRule for IteBoolComplementBranches {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let (c, t, e) = (&terms[0], &terms[1], &terms[2]);
        if !t.is_bool() {
            return None;
        }

        // ite(c, x, !x) => eq(c, x)
        if e == !t {
            return Some(c.op1(Eq, t));
        }
        // ite(c, !x, x) => xor(c, x)
        if t == !e {
            return Some(c ^ e);
        }
        None
    }
}

struct IteBoolBranchConst;
impl RewriteRule for IteBoolBranchConst {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let (c, t, e) = (&terms[0], &terms[1], &terms[2]);
        if !t.is_bool() {
            return None;
        }

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
        None
    }
}

pub(crate) fn ite_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    let pipeline = RewritePipeline::new(ctx.level)
        .with_rule(IteConstCond)
        .with_rule(IteSameBranches)
        .with_rule(IteNotCondSwap)
        .with_rule(IteBoolComplementBranches)
        .with_rule(IteBoolBranchConst);
    pipeline.apply(terms)
}

struct ConcatConst;
impl RewriteRule for ConcatConst {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];
        let (xc, yc) = (x.try_bv_const()?, y.try_bv_const()?);
        let mut c = yc.clone();
        c.extend(xc.iter());
        Some(Term::bv_const(c))
    }
}

struct ConcatAssocConstPrefix;
impl RewriteRule for ConcatAssocConstPrefix {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];

        // concat(c1, concat(c2, t)) => concat(concat(c1,c2), t)
        // (exposes constant folding on concat(c1,c2))
        x.try_bv_const()?;
        let yop = y.try_op()?;
        if yop.op != Concat {
            return None;
        }
        yop[0].try_bv_const()?;

        let hi = Term::new_op(Concat, [x.clone(), yop[0].clone()]);
        Some(hi.op1(Concat, &yop[1]))
    }
}

struct ConcatSignExtBySlice;
impl RewriteRule for ConcatSignExtBySlice {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];
        if y.bv_len() == 0 || x.bv_len() != 1 {
            return None;
        }
        let xop = x.try_op()?;
        if xop.op != Slice || xop[0] != *y {
            return None;
        }
        let idx = y.bv_len() - 1;
        if xop[1].bv_len() == idx && xop[2].bv_len() == idx {
            return Some(Term::new_op(Sext, [y.clone(), Term::bool_const(false)]));
        }
        None
    }
}

struct ConcatSignExtBySextSlice;
impl RewriteRule for ConcatSignExtBySextSlice {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];
        if y.bv_len() == 0 || x.bv_len() != 1 {
            return None;
        }

        let yop = y.try_op()?;
        if yop.op != Sext {
            return None;
        }
        let xop = x.try_op()?;
        if xop.op != Slice || xop[0] != yop[0] {
            return None;
        }
        let inner = &yop[0];
        if inner.bv_len() == 0 {
            return None;
        }
        let idx = inner.bv_len() - 1;
        if xop[1].bv_len() == idx && xop[2].bv_len() == idx {
            return Some(Term::new_op(
                Sext,
                [
                    inner.clone(),
                    Term::bv_const(BitVec::zero(yop[1].bv_len() + 1)),
                ],
            ));
        }
        None
    }
}

struct ConcatSignExtByMsbTerm;
impl RewriteRule for ConcatSignExtByMsbTerm {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];
        if y.bv_len() == 0 || x.bv_len() != 1 {
            return None;
        }
        if let Some(msb) = msb_bit_term(y)
            && msb == *x
        {
            return Some(Term::new_op(Sext, [y.clone(), Term::bool_const(false)]));
        }
        None
    }
}

pub(crate) fn concat_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    let pipeline = RewritePipeline::new(ctx.level)
        .with_rule(ConcatConst)
        .with_rule(ConcatAssocConstPrefix)
        .with_rule(ConcatSignExtBySlice)
        .with_rule(ConcatSignExtBySextSlice)
        .with_rule(ConcatSignExtByMsbTerm);
    pipeline.apply(terms)
}

struct SextZeroExt;
impl RewriteRule for SextZeroExt {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let ext = terms[1].bv_len();
        if ext == 0 {
            return Some(x.clone());
        }
        None
    }
}

struct SextMergeNested;
impl RewriteRule for SextMergeNested {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let ext = terms[1].bv_len();
        let xop = x.try_op()?;
        if xop.op != Sext {
            return None;
        }
        let inner = &xop[0];
        let inner_ext = xop[1].bv_len();
        Some(Term::new_op(
            Sext,
            [inner.clone(), Term::bv_const(BitVec::zero(inner_ext + ext))],
        ))
    }
}

pub(crate) fn sext_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    let pipeline = RewritePipeline::new(ctx.level)
        .with_rule(SextZeroExt)
        .with_rule(SextMergeNested);
    pipeline.apply(terms)
}

struct SliceWholeRange;
impl RewriteRule for SliceWholeRange {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let s = &terms[0];
        let l = terms[2].bv_len();
        let h = terms[1].bv_len();
        if l == 0 && h == s.bv_len() - 1 {
            return Some(s.clone());
        }
        None
    }
}

struct SliceOfSlice;
impl RewriteRule for SliceOfSlice {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let s = &terms[0];
        let l = terms[2].bv_len();
        let h = terms[1].bv_len();
        let sop = s.try_op()?;
        if sop.op != Slice {
            return None;
        }
        let base = &sop[0];
        let inner_l = sop[2].bv_len();
        let new_l = inner_l + l;
        let new_h = inner_l + h;
        Some(base.slice(new_l, new_h))
    }
}

struct SliceOfConcat;
impl RewriteRule for SliceOfConcat {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let s = &terms[0];
        let l = terms[2].bv_len();
        let h = terms[1].bv_len();
        let sop = s.try_op()?;
        if sop.op != Concat {
            return None;
        }

        let hi = &sop[0];
        let lo = &sop[1];
        let lo_len = lo.bv_len();
        if h < lo_len {
            return Some(lo.slice(l, h));
        }
        if l >= lo_len {
            return Some(hi.slice(l - lo_len, h - lo_len));
        }

        let hi_part = hi.slice(0, h - lo_len);
        let lo_part = lo.slice(l, lo_len - 1);
        Some(Term::new_op(Concat, [hi_part, lo_part]))
    }
}

pub(crate) fn slice_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    let pipeline = RewritePipeline::new(ctx.level)
        .with_rule(SliceWholeRange)
        .with_rule(SliceOfSlice)
        .with_rule(SliceOfConcat);
    pipeline.apply(terms)
}

struct SubByZero;
impl RewriteRule for SubByZero {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let (x, y) = (&terms[0], &terms[1]);
        let yc = y.try_bv_const()?;
        if yc.is_zero() {
            return Some(x.clone());
        }
        None
    }
}

struct SubBv1MinusOne;
impl RewriteRule for SubBv1MinusOne {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let (x, y) = (&terms[0], &terms[1]);
        let yc = y.try_bv_const()?;
        if x.bv_len() == 1 && yc.is_one() {
            return Some(!x.clone());
        }
        None
    }
}

pub(crate) fn sub_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    let pipeline = RewritePipeline::new(ctx.level)
        .with_rule(SubByZero)
        .with_rule(SubBv1MinusOne);
    pipeline.apply(terms)
}

struct MulByZero;
impl RewriteRule for MulByZero {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let xc = x.try_bv_const()?;
        if xc.is_zero() {
            return Some(x.clone());
        }
        None
    }
}

struct MulByOne;
impl RewriteRule for MulByOne {
    fn apply(&self, terms: &[Term]) -> TermResult {
        let x = &terms[0];
        let y = &terms[1];
        let xc = x.try_bv_const()?;
        if xc.is_one() {
            return Some(y.clone());
        }
        None
    }
}

pub(crate) fn mul_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    let pipeline = RewritePipeline::new(ctx.level)
        .with_rule(MulByZero)
        .with_rule(MulByOne);
    pipeline.apply(terms)
}

pub(crate) fn udiv_simplify(ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
    // Placeholder: no rewrite rules yet.
    RewritePipeline::new(ctx.level).apply(terms)
}

fn op_simplify(ctx: &SimplifyCtx, op: FolOp, terms: &[Term]) -> TermResult {
    // Constant propagation
    if terms.iter().all(|t| t.is_const()) {
        let vals: Vec<Value> = terms
            .iter()
            .map(|t| Value::Bv(t.try_bv_const().unwrap().clone().into()))
            .collect();
        let result = op.simulate(&vals);
        let lbv = result.into_bv().unwrap();
        return Some(Term::bv_const(BitVec::from(lbv)));
    }

    // Idempotent: op(a, a) = a
    if op.traits().contains(OpTrait::Idempotent) && terms[0] == terms[1] {
        return Some(terms[0].clone());
    }

    // Involutive: op(op(a)) = a
    if op.traits().contains(OpTrait::Involutive)
        && let Some(inner_op) = terms[0].try_op()
        && inner_op.op == op
    {
        return Some(inner_op.terms[0].clone());
    }

    op.simplify(ctx, terms).or_else(|| {
        if op.traits().contains(OpTrait::Commutative) {
            debug_assert!(terms.len() == 2);
            op.simplify(ctx, &[terms[1].clone(), terms[0].clone()])
        } else {
            None
        }
    })
}

impl FolOp {
    pub fn simplify(&self, ctx: &SimplifyCtx, terms: &[Term]) -> TermResult {
        match self {
            FolOp::Not => not_simplify(ctx, terms),
            FolOp::And => and_simplify(ctx, terms),
            FolOp::Or => or_simplify(ctx, terms),
            FolOp::Xor => xor_simplify(ctx, terms),
            FolOp::Eq => eq_simplify(ctx, terms),
            FolOp::Ult => ult_simplify(ctx, terms),
            FolOp::Ite => ite_simplify(ctx, terms),
            FolOp::Concat => concat_simplify(ctx, terms),
            FolOp::Sext => sext_simplify(ctx, terms),
            FolOp::Slice => slice_simplify(ctx, terms),
            FolOp::Sub => sub_simplify(ctx, terms),
            FolOp::Mul => mul_simplify(ctx, terms),
            FolOp::Udiv => udiv_simplify(ctx, terms),
            _ => None,
        }
    }
}

impl Term {
    pub fn simplify(&self, map: &mut GHashMap<Term, Term>) -> Term {
        self.simplify_with_ctx(&SimplifyCtx::default(), map)
    }

    pub fn simplify_with_ctx(&self, ctx: &SimplifyCtx, map: &mut GHashMap<Term, Term>) -> Term {
        if let Some(res) = map.get(self) {
            return res.clone();
        }
        let simp = match ctx.level {
            OptLevel::O0 => self.clone(),
            _ => {
                if let Some(op_term) = self.try_op() {
                    let terms: Vec<Term> = op_term
                        .terms
                        .iter()
                        .map(|s| s.simplify_with_ctx(ctx, map))
                        .collect();
                    if let Some(res) = op_simplify(ctx, op_term.op, &terms) {
                        res.simplify_with_ctx(ctx, map)
                    } else {
                        Term::new_op(op_term.op, terms)
                    }
                } else {
                    self.clone()
                }
            }
        };
        map.insert(self.clone(), simp);
        map.get(self).unwrap().clone()
    }
}
