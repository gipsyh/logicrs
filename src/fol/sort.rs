use std::fmt::{self, Debug};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Sort {
    Bv(usize),
    Array(usize, usize),
}

impl Sort {
    #[inline]
    pub fn bool() -> Self {
        Sort::Bv(1)
    }

    #[inline]
    pub fn is_bool(&self) -> bool {
        matches!(self, Self::Bv(1))
    }

    #[inline]
    pub fn size(&self) -> usize {
        match self {
            Sort::Bv(s) => *s,
            Sort::Array(i, e) => {
                let i = (*i).try_into().unwrap();
                let shifted = 1usize.checked_shl(i).unwrap();
                shifted.checked_mul(*e).unwrap()
            }
        }
    }

    #[inline]
    pub fn bv(&self) -> usize {
        if let Sort::Bv(w) = self { *w } else { panic!() }
    }

    #[inline]
    pub fn array(&self) -> (usize, usize) {
        if let Sort::Array(i, e) = self {
            (*i, *e)
        } else {
            panic!()
        }
    }

    #[inline]
    pub fn is_array(&self) -> bool {
        matches!(self, Self::Array(_, _))
    }
}

impl Debug for Sort {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Sort::Bv(w) => write!(f, "Bv{w}"),
            Sort::Array(w, d) => write!(f, "Array{w},{d}"),
        }
    }
}
