use crate::{
    Lbool, LboolVec,
    fol::{Sort, Term},
};
use enum_as_inner::EnumAsInner;
use giputils::hash::GHashMap;

#[derive(Clone, Debug, EnumAsInner)]
pub enum Value {
    Bv(LboolVec),
    Array(GHashMap<usize, LboolVec>),
}

impl Value {
    #[inline]
    pub fn default_from(sort: &Sort) -> Self {
        match sort {
            Sort::Bv(w) => Value::Bv(LboolVec::from_elem(Lbool::NONE, *w)),
            Sort::Array(_, _) => Value::Array(GHashMap::default()),
        }
    }
}

#[derive(Clone, Debug)]
pub struct BvTermValue {
    t: Term,
    v: LboolVec,
}

impl BvTermValue {
    #[inline]
    pub fn t(&self) -> &Term {
        &self.t
    }

    #[inline]
    pub fn v(&self) -> &LboolVec {
        &self.v
    }

    #[inline]
    pub fn new(t: Term, v: LboolVec) -> Self {
        Self { t, v }
    }

    /// Eq Term
    #[inline]
    pub fn teq(&self) -> Term {
        if self.v.mask().is_ones() {
            self.t.teq(Term::bv_const(self.v.v().clone()))
        } else {
            let m = &self.t & Term::bv_const(self.v.mask().clone());
            m.teq(Term::bv_const(self.v.v().clone()))
        }
    }
}

impl AsRef<BvTermValue> for BvTermValue {
    #[inline]
    fn as_ref(&self) -> &BvTermValue {
        self
    }
}

impl AsMut<BvTermValue> for BvTermValue {
    #[inline]
    fn as_mut(&mut self) -> &mut BvTermValue {
        self
    }
}

#[derive(Clone, Debug)]
pub struct ArrayTermValue {
    pub t: Term,
    pub v: GHashMap<usize, LboolVec>,
}

impl ArrayTermValue {
    #[inline]
    pub fn new(t: Term, v: GHashMap<usize, LboolVec>) -> Self {
        Self { t, v }
    }

    /// Eq Term
    #[inline]
    pub fn teq(&self) -> Term {
        todo!()
    }
}

#[derive(Clone, Debug)]
pub struct TermValue {
    t: Term,
    v: Value,
}

impl TermValue {
    #[inline]
    pub fn new(t: Term, v: Value) -> Self {
        Self { t, v }
    }

    #[inline]
    pub fn t(&self) -> &Term {
        &self.t
    }

    pub fn into_bv(&self) -> BvTermValue {
        BvTermValue {
            t: self.t.clone(),
            v: self.v.clone().into_bv().unwrap(),
        }
    }

    pub fn into_array(&self) -> ArrayTermValue {
        ArrayTermValue {
            t: self.t.clone(),
            v: self.v.clone().into_array().unwrap(),
        }
    }
}

impl<B: AsRef<BvTermValue>> From<B> for TermValue {
    fn from(b: B) -> Self {
        let b = b.as_ref();
        Self {
            t: b.t().clone(),
            v: Value::Bv(b.v().clone()),
        }
    }
}
