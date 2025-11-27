macro_rules! op_trait_impl {
    (sort $impl:expr) => {
        #[inline]
        fn sort(&self, terms: &[crate::fol::Term]) -> crate::fol::Sort {
            debug_assert!(self.num_operand() == terms.len());
            $impl(terms)
        }
    };
    (normalize $impl:expr) => {
        #[inline]
        fn normalize(
            &self,
            tm: &mut crate::fol::TermManager,
            terms: &[crate::fol::Term],
        ) -> crate::fol::Term {
            debug_assert!(self.num_operand() == terms.len());
            $impl(tm, terms)
        }
    };
    (simplify $impl:expr) => {
        #[inline]
        fn simplify(&self, terms: &[crate::fol::Term]) -> crate::fol::TermResult {
            debug_assert!(self.num_operand() == terms.len());
            $impl(terms)
        }
    };
    (bitblast $impl:expr) => {
        #[inline]
        fn bitblast(&self, terms: &[crate::fol::TermVec]) -> crate::fol::TermVec {
            debug_assert!(self.num_operand() == terms.len());
            $impl(terms)
        }
    };
    (cnf_encode $impl:expr) => {
        #[inline]
        fn cnf_encode(&self, dc: &mut crate::DagCnf, terms: &[crate::Lit]) -> crate::Lit {
            $impl(dc, terms)
        }
    };
}

macro_rules! define_core_op {
    ($name:ident, $num_operand:expr, $($be_impl:ident: $impl:expr),*) => {
        #[derive(Hash, Debug, PartialEq, Clone, Copy)]
        pub struct $name;
        inventory::submit! {crate::fol::op::DynOpCollect(|| crate::fol::op::DynOp::create($name))}
        impl crate::fol::op::Op for $name {
            #[inline]
            fn num_operand(&self) -> usize {
                $num_operand
            }

            #[inline]
            fn is_core(&self) -> bool {
                true
            }

            #[inline]
            fn normalize(&self, _terms: &[crate::fol::Term]) -> crate::fol::Term {
                panic!("{:?} not support normalize", self);
            }

            $(
                crate::fol::op::define::op_trait_impl!($be_impl $impl);
            )*
        }
        impl std::fmt::Display for $name {
            #[inline]
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{self:?}")
            }
        }
    };
}

macro_rules! define_non_core_op {
    ($name:ident, $num_operand:expr) => {
        #[derive(Hash, Debug, PartialEq, Clone, Copy)]
        pub struct $name;
        inventory::submit! {crate::fol::fol::op::DynOpCollect(|| crate::fol::op::DynOp::new($name))}
        impl crate::fol::op::Op for $name {
            #[inline]
            fn num_operand(&self) -> usize {
                $num_operand
            }
        }
        impl std::fmt::Display for $name {
            #[inline]
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{self:?}")
            }
        }
    };
    ($name:ident, $num_operand:expr, $normalize:expr) => {
        #[derive(Hash, Debug, PartialEq, Clone, Copy)]
        pub struct $name;
        inventory::submit! {crate::fol::op::DynOpCollect(|| crate::fol::op::DynOp::create($name))}
        impl crate::fol::op::Op for $name {
            #[inline]
            fn num_operand(&self) -> usize {
                $num_operand
            }

            #[inline]
            fn sort(&self, _terms: &[crate::fol::Term]) -> crate::fol::Sort {
                panic!("{:?} not support sort", self);
            }

            #[inline]
            fn normalize(&self, terms: &[crate::fol::Term]) -> crate::fol::Term {
                debug_assert!(self.num_operand() == terms.len());
                $normalize(terms)
            }
        }
        impl std::fmt::Display for $name {
            #[inline]
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{self:?}")
            }
        }
    };
}

macro_rules! define_core_fold_op {
    ($name:ident, $($be_impl:ident: $impl:expr),*) => {
        #[derive(Hash, Debug, PartialEq, Clone, Copy)]
        pub struct $name;
        inventory::submit! {crate::fol::op::DynOpCollect(|| crate::fol::op::DynOp::create($name))}
        impl crate::fol::op::Op for $name {
            #[inline]
            fn num_operand(&self) -> usize {
                panic!("fold op has no num_operand");
            }

            #[inline]
            fn is_core(&self) -> bool {
                true
            }

            #[inline]
            fn normalize(&self, _terms: &[crate::fol::Term]) -> crate::fol::Term {
                panic!("{:?} not support normalize", self);
            }

            $(
                crate::fol::op::define::op_trait_impl!($be_impl $impl);
            )*
        }
        impl std::fmt::Display for $name {
            #[inline]
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{self:?}")
            }
        }
    };
}

pub(crate) use define_core_fold_op;
pub(crate) use define_core_op;
pub(crate) use define_non_core_op;
pub(crate) use op_trait_impl;
