mod core_op;
mod define;
mod other_op;

use super::term::Term;
use crate::fol::{Sort, TermResult, TermVec};
use crate::{DagCnf, Lit};
pub use core_op::*;
use giputils::hash::GHashMap;
use lazy_static::lazy_static;
pub use other_op::*;
use std::fmt::{self, Display};
use std::{
    any::TypeId,
    borrow::Borrow,
    fmt::Debug,
    hash::{Hash, Hasher},
    ops::Deref,
    rc::Rc,
};

pub trait Op: Debug + 'static {
    #[inline]
    fn type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }

    #[inline]
    fn is_core(&self) -> bool {
        false
    }

    fn num_operand(&self) -> usize;

    #[inline]
    fn sort(&self, terms: &[Term]) -> Sort {
        terms[0].sort()
    }

    fn normalize(&self, _terms: &[Term]) -> Term {
        panic!("{self:?} not support normalize");
    }

    fn simplify(&self, _terms: &[Term]) -> TermResult {
        None
    }

    fn bitblast(&self, _terms: &[TermVec]) -> TermVec {
        panic!("{self:?} not support biblast");
    }

    fn cnf_encode(&self, _dc: &mut DagCnf, _terms: &[Lit]) -> Lit {
        panic!("{self:?} not support cnf_encode");
    }
}

#[derive(Clone)]
pub struct DynOp {
    op: Rc<dyn Op>,
}

impl DynOp {
    #[inline]
    fn create(op: impl Op) -> Self {
        Self { op: Rc::new(op) }
    }
}

impl<T: Op> From<T> for DynOp {
    #[inline]
    fn from(op: T) -> Self {
        OP_MAP
            .get(&op.type_id())
            .unwrap_or_else(|| panic!("unsupport {op:?} op!"))
            .clone()
    }
}

impl Deref for DynOp {
    type Target = dyn Op;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.op.borrow()
    }
}

impl Debug for DynOp {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.op.fmt(f)
    }
}

impl Display for DynOp {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.op.fmt(f)
    }
}

impl Hash for DynOp {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.op.type_id().hash(state);
    }
}

impl PartialEq for DynOp {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.op.type_id() == other.op.type_id()
    }
}

impl std::cmp::Eq for DynOp {}

impl<O: Op> PartialEq<O> for DynOp {
    #[inline]
    fn eq(&self, other: &O) -> bool {
        self.op.type_id() == other.type_id()
    }
}

unsafe impl Send for DynOp {}

unsafe impl Sync for DynOp {}

struct DynOpCollect(fn() -> DynOp);

inventory::collect!(DynOpCollect);

lazy_static! {
    static ref OP_MAP: GHashMap<TypeId, DynOp> = {
        let mut m = GHashMap::new();
        for op in inventory::iter::<DynOpCollect> {
            let op = op.0();
            m.insert(op.type_id(), op);
        }
        m
    };
    static ref STR_OP_MAP: GHashMap<String, DynOp> = {
        let mut m = GHashMap::new();
        for op in inventory::iter::<DynOpCollect> {
            let op = op.0();
            m.insert(format!("{op}").to_lowercase(), op);
        }
        m
    };
}

impl From<&str> for DynOp {
    #[inline]
    fn from(value: &str) -> Self {
        STR_OP_MAP
            .get(&value.to_lowercase())
            .unwrap_or_else(|| panic!("unsupport {value} op!"))
            .clone()
    }
}

// pub enum BiOpType {
//     Saddo,
//     Uaddo,
//     Sdivo,
//     Udivo,
//     Smulo,
//     Umulo,
//     Ssubo,
//     Usubo,
// }
