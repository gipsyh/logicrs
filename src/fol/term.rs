use super::op::{Add, And, Ite, Neg, Not, Or, Sub, Xor};
use super::{op::DynOp, sort::Sort};
use crate::fol::op::{Concat, Slice};
use crate::fol::{TermVec, Value, op};
use giputils::bitvec::BitVec;
use giputils::grc::Grc;
use giputils::hash::GHashMap;
use std::cell::UnsafeCell;
use std::fmt::{self, Debug};
use std::hash;
use std::iter::once;
use std::ops::Index;
use std::{hash::Hash, ops::Deref};

#[derive(Clone)]
pub struct Term {
    pub(crate) inner: Grc<TermInner>,
}

impl Term {
    #[inline]
    pub fn bool_const(c: bool) -> Term {
        tm().new_term(TermType::Const(BitVec::from(&[c])), Sort::Bv(1))
    }

    #[inline]
    pub fn bv_const(c: BitVec) -> Term {
        let sort = Sort::Bv(c.len());
        tm().new_term(TermType::Const(c), sort)
    }

    #[inline]
    pub fn new_op(op: impl Into<DynOp>, terms: impl IntoIterator<Item = impl AsRef<Term>>) -> Term {
        let op: DynOp = op.into();
        let terms: Vec<Term> = terms.into_iter().map(|t| t.as_ref().clone()).collect();
        debug_assert!(!terms.is_empty());
        if !op.is_core() {
            return op.normalize(&terms);
        }
        let sort = op.sort(&terms);
        let term = TermType::Op(OpTerm::new(op, terms));
        tm().new_term(term, sort)
    }

    #[inline]
    pub fn new_var(sort: Sort) -> Term {
        tm().new_var(sort)
    }

    #[inline]
    pub fn new_op_fold(
        op: impl Into<DynOp> + Copy,
        terms: impl IntoIterator<Item = impl AsRef<Term>>,
    ) -> Term {
        let mut terms = terms.into_iter();
        let acc = terms.next().unwrap().as_ref().clone();
        terms.fold(acc, |acc, x| Self::new_op(op, &[acc, x.as_ref().clone()]))
    }

    /// can only be used for bool terms
    pub fn new_ands(terms: impl IntoIterator<Item = impl AsRef<Term>>) -> Term {
        terms.into_iter().fold(Term::bool_const(true), |acc, x| {
            Self::new_op(op::And, &[acc, x.as_ref().clone()])
        })
    }

    /// can only be used for bool terms
    pub fn new_ors(terms: impl IntoIterator<Item = impl AsRef<Term>>) -> Term {
        terms.into_iter().fold(Term::bool_const(false), |acc, x| {
            Self::new_op(op::Or, &[acc, x.as_ref().clone()])
        })
    }

    #[inline]
    pub fn new_op_elementwise(
        op: impl Into<DynOp> + Copy,
        x: impl IntoIterator<Item = impl AsRef<Term>>,
        y: impl IntoIterator<Item = impl AsRef<Term>>,
    ) -> TermVec {
        x.into_iter()
            .zip(y)
            .map(|(x, y)| Self::new_op(op, [x.as_ref(), y.as_ref()]))
            .collect()
    }
}

impl Term {
    #[inline]
    pub fn sort(&self) -> Sort {
        self.inner.sort()
    }

    #[inline]
    pub fn is_bool(&self) -> bool {
        self.sort().is_bool()
    }

    #[inline]
    pub fn is_const(&self) -> bool {
        matches!(self.deref(), TermType::Const(_))
    }

    #[inline]
    pub fn is_var(&self) -> bool {
        matches!(self.deref(), TermType::Var(_))
    }

    #[inline]
    pub fn is_op(&self) -> bool {
        matches!(self.deref(), TermType::Op(_))
    }

    #[inline]
    pub fn try_op(&self) -> Option<&OpTerm> {
        if let TermType::Op(op) = self.deref() {
            Some(op)
        } else {
            None
        }
    }

    #[inline]
    pub fn bv_len(&self) -> usize {
        self.sort().bv()
    }

    #[inline]
    pub fn try_bv_const(&self) -> Option<&BitVec> {
        match self.deref() {
            TermType::Const(c) => Some(c),
            _ => None,
        }
    }

    #[inline]
    pub fn op<'a>(
        &'a self,
        op: impl Into<DynOp>,
        terms: impl IntoIterator<Item = impl AsRef<Term> + 'a>,
    ) -> Term {
        let terms = once(self.clone()).chain(terms.into_iter().map(|l| l.as_ref().clone()));
        Self::new_op(op.into(), terms)
    }

    #[inline]
    pub fn op0(&self, op: impl Into<DynOp>) -> Term {
        Self::new_op(op.into(), [self])
    }

    #[inline]
    pub fn op1(&self, op: impl Into<DynOp>, x: impl AsRef<Term>) -> Term {
        Self::new_op(op.into(), [self, x.as_ref()])
    }

    #[inline]
    pub fn op2(&self, op: impl Into<DynOp>, x: impl AsRef<Term>, y: impl AsRef<Term>) -> Term {
        Self::new_op(op.into(), [self, x.as_ref(), y.as_ref()])
    }

    #[inline]
    pub fn imply(&self, x: impl AsRef<Term>) -> Term {
        self.op1(op::Implies, x)
    }

    #[inline]
    pub fn not_if(&self, c: bool) -> Term {
        if c { !self } else { self.clone() }
    }

    #[inline]
    pub fn ite(&self, t: impl AsRef<Term>, e: impl AsRef<Term>) -> Term {
        self.op2(Ite, t, e)
    }

    #[inline]
    pub fn slice(&self, l: usize, h: usize) -> Term {
        let h = Self::bv_const(BitVec::zero(h));
        let l = Self::bv_const(BitVec::zero(l));
        self.op2(Slice, &h, &l)
    }

    #[inline]
    pub fn concat(&self, o: impl AsRef<Term>) -> Term {
        self.op1(Concat, o)
    }

    /// Term Eq, different from PartialEq trait
    #[inline]
    pub fn teq(&self, o: impl AsRef<Term>) -> Term {
        self.op1(op::Eq, o)
    }

    /// Term Neq, different from PartialEq trait
    #[inline]
    pub fn tneq(&self, o: impl AsRef<Term>) -> Term {
        self.op1(op::Neq, o)
    }

    #[inline]
    pub fn mk_bv_const_zero(&self) -> Term {
        Term::bv_const(BitVec::zero(self.bv_len()))
    }

    #[inline]
    pub fn mk_bv_const_one(&self) -> Term {
        Term::bv_const(BitVec::one(self.bv_len()))
    }

    #[inline]
    pub fn mk_bv_const_ones(&self) -> Term {
        Term::bv_const(BitVec::ones(self.bv_len()))
    }

    #[inline]
    pub fn cached_apply(
        &self,
        r: &impl Fn(&Term) -> Option<Term>,
        map: &mut GHashMap<Term, Term>,
    ) -> Term {
        if let Some(r) = map.get(self) {
            return r.clone();
        }
        let r = if let Some(r) = r(self) {
            r
        } else {
            self.try_op()
                .map(|op_term| {
                    let a: Vec<Term> = op_term
                        .terms
                        .iter()
                        .map(|t| t.cached_apply(r, map))
                        .collect();
                    Term::new_op(op_term.op.clone(), a)
                })
                .unwrap_or(self.clone())
        };
        map.insert(self.clone(), r.clone());
        r
    }

    pub fn apply(&self, r: impl Fn(&Term) -> Option<Term>) -> Term {
        self.cached_apply(&r, &mut GHashMap::new())
    }

    pub fn simulate(&self, val: &mut GHashMap<Term, Value>) -> Value {
        if let Some(v) = val.get(self) {
            return v.clone();
        }
        let v = match self.deref() {
            TermType::Const(c) => Value::Bv(c.clone().into()),
            TermType::Var(_) => Value::default_from(&self.sort()),
            TermType::Op(op_term) => {
                let child_vals: Vec<Value> =
                    op_term.terms.iter().map(|t| t.simulate(val)).collect();
                op_term.op.simulate(&child_vals)
            }
        };
        val.insert(self.clone(), v.clone());
        v
    }
}

impl Deref for Term {
    type Target = TermType;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.inner.ty
    }
}

impl Hash for Term {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.inner.hash(state);
    }
}

impl Debug for Term {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.deref().fmt(f)
    }
}

impl<T: AsRef<Term>> PartialEq<T> for Term {
    #[inline]
    fn eq(&self, other: &T) -> bool {
        let other = other.as_ref();
        self.inner == other.inner
    }
}

impl PartialEq<Term> for &Term {
    #[inline]
    fn eq(&self, other: &Term) -> bool {
        self.inner == other.inner
    }
}

impl Eq for Term {}

impl AsRef<Term> for Term {
    #[inline]
    fn as_ref(&self) -> &Term {
        self
    }
}

impl Drop for Term {
    #[inline]
    fn drop(&mut self) {
        // let g = self.clone();
        // tm().tgc.collect(g);
    }
}

macro_rules! impl_unary_ops {
    ($trait:ident, $method:ident, $op:expr) => {
        impl std::ops::$trait for Term {
            type Output = Term;

            #[inline]
            fn $method(self) -> Self::Output {
                self.op0($op)
            }
        }

        impl std::ops::$trait for &Term {
            type Output = Term;

            #[inline]
            fn $method(self) -> Self::Output {
                self.op0($op)
            }
        }

        impl std::ops::$trait for &mut Term {
            type Output = Term;

            #[inline]
            fn $method(self) -> Self::Output {
                self.op0($op)
            }
        }
    };
}

impl_unary_ops!(Not, not, Not);
impl_unary_ops!(Neg, neg, Neg);

macro_rules! impl_biops {
    ($trait:ident, $method:ident, $op:expr) => {
        impl<T: AsRef<Term>> std::ops::$trait<T> for Term {
            type Output = Term;

            #[inline]
            fn $method(self, rhs: T) -> Self::Output {
                self.op1($op, rhs.as_ref())
            }
        }

        impl<T: AsRef<Term>> std::ops::$trait<T> for &Term {
            type Output = Term;

            #[inline]
            fn $method(self, rhs: T) -> Self::Output {
                self.op1($op, rhs.as_ref())
            }
        }

        impl<T: AsRef<Term>> std::ops::$trait<T> for &mut Term {
            type Output = Term;

            #[inline]
            fn $method(self, rhs: T) -> Self::Output {
                self.op1($op, rhs.as_ref())
            }
        }
    };
}

impl_biops!(BitAnd, bitand, And);
impl_biops!(BitOr, bitor, Or);
impl_biops!(BitXor, bitxor, Xor);
impl_biops!(Add, add, Add);
impl_biops!(Sub, sub, Sub);

pub struct TermInner {
    sort: Sort,
    ty: TermType,
}

impl TermInner {
    #[inline]
    pub fn sort(&self) -> Sort {
        self.sort
    }
}

impl Debug for TermInner {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.ty {
            TermType::Const(c) => c.fmt(f),
            TermType::Var(v) => write!(f, "Var{}, {:?}", *v, self.sort),
            TermType::Op(o) => o.fmt(f),
        }
    }
}

impl Deref for TermInner {
    type Target = TermType;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.ty
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum TermType {
    Const(BitVec),
    Var(usize),
    Op(OpTerm),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct OpTerm {
    pub op: DynOp,
    pub terms: Vec<Term>,
}

impl OpTerm {
    #[inline]
    fn new(op: impl Into<DynOp>, terms: Vec<Term>) -> Self {
        Self {
            op: op.into(),
            terms: terms.to_vec(),
        }
    }
}

impl Debug for OpTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.op.fmt(f)?;
        self.terms.fmt(f)
    }
}

impl Index<usize> for OpTerm {
    type Output = Term;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        &self.terms[index]
    }
}

#[derive(Clone, Default, PartialEq, Eq, Debug)]
pub struct TermGC {
    garbage: Vec<Term>,
}

impl TermGC {
    #[inline]
    pub fn collect(&mut self, term: Term) {
        self.garbage.push(term);
    }
}

struct TermManager {
    _tgc: TermGC,
    avl_vid: usize,
    map: GHashMap<TermType, Term>,
}

impl TermManager {
    #[inline]
    fn new() -> Self {
        Self {
            _tgc: TermGC {
                garbage: Vec::new(),
            },
            avl_vid: 0,
            map: GHashMap::new(),
        }
    }

    #[inline]
    fn new_term(&mut self, ty: TermType, sort: Sort) -> Term {
        match self.map.get(&ty) {
            Some(term) => term.clone(),
            None => {
                let term = Term {
                    inner: Grc::new(TermInner {
                        sort,
                        ty: ty.clone(),
                    }),
                };
                self.map.insert(ty, term.clone());
                term
            }
        }
    }

    #[inline]
    fn new_var(&mut self, sort: Sort) -> Term {
        let id = self.avl_vid;
        self.avl_vid += 1;
        let term = TermType::Var(id);
        self.new_term(term, sort)
    }

    #[inline]
    #[allow(unused)]
    fn garbage_collect(&mut self) {}
}

thread_local! {
    static TERM_MANAGER: UnsafeCell<TermManager> = UnsafeCell::new(TermManager::new());
}

#[inline]
fn tm() -> &'static mut TermManager {
    TERM_MANAGER.with(|m| unsafe { &mut *m.get() })
}
