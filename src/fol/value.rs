use crate::fol::{Sort, Term};
use giputils::{bitvec::BitVec, hash::GHashMap};

#[derive(Clone, Debug)]
pub enum Value {
    Bv(BitVec),
    Array(GHashMap<usize, BitVec>),
}

impl Value {
    #[inline]
    pub fn default_from(sort: &Sort) -> Self {
        match sort {
            Sort::Bv(w) => Value::Bv(BitVec::from_elem(*w, false)),
            Sort::Array(_, _) => Value::Array(GHashMap::default()),
        }
    }
}

#[derive(Clone, Debug)]
pub struct BvTermValue {
    t: Term,
    v: BitVec,
}

impl BvTermValue {
    #[inline]
    pub fn t(&self) -> &Term {
        &self.t
    }

    #[inline]
    pub fn v(&self) -> &BitVec {
        &self.v
    }

    #[inline]
    pub fn new(t: Term, v: BitVec) -> Self {
        Self { t, v }
    }

    /// Eq Term
    #[inline]
    pub fn teq(&self) -> Term {
        self.t.teq(&Term::bv_const(self.v.clone()))
    }
}

#[derive(Clone, Debug)]
pub struct ArrayTermValue {
    pub t: Term,
    pub v: GHashMap<usize, BitVec>,
}

impl ArrayTermValue {
    #[inline]
    pub fn new(t: Term, v: GHashMap<usize, BitVec>) -> Self {
        Self { t, v }
    }

    /// Eq Term
    #[inline]
    pub fn teq(&self) -> Term {
        todo!()
    }
}

#[derive(Clone, Debug)]
pub enum TermValue {
    Bv(BvTermValue),
    Array(ArrayTermValue),
}

impl TermValue {
    #[inline]
    pub fn t(&self) -> &Term {
        match self {
            TermValue::Bv(t) => &t.t,
            TermValue::Array(t) => &t.t,
        }
    }
}
