pub(crate) use {
    std::{
        cmp, fmt, hash, iter, ops, mem,
        marker::PhantomData,
        ops::{ControlFlow, Try, FromResidual, Residual},
        sync::{Arc, RwLock},
        num::NonZero,
    },
    im::{ordset, ordmap, OrdSet, OrdMap},
    num::{One, Zero, CheckedSub, BigUint},
    small_bit_vec::SmallBitVec,
    indexmap::IndexSet,
    lazy_static::lazy_static,
    derive_where::derive_where,
    crate::{
        scheme::Scheme,
        core::{Contextual, Ctx, Ty, TyKind, Tm, Stuck, Scope},
        usages::Usages,
        non_zero_big_uint::NonZeroBigUint,
        raw::{
            Substitute, Weaken, RawCtx, RawCtxCons, RawTy, RawTm, RawStuck, RawScope, RawScopeKind,
            RawTyKind, RawTmKind, RawStuckKind, RawTyped, RawTypedKind,
            //RawContextualTuple, SubstituteTuple, RawPack, 
            raw_scope, raw_scope_2, raw_scope_3, try_raw_scope,
            RawNat, MaxAll, AddAll, MulAll,
        },
        intern::{Interner, Intern},
        util::as_equal,
    },
};

#[allow(unused)]
#[cfg(debug_assertions)]
pub(crate) use {
    crate::sanity_check::SanityCheck,
    debug::{indent_scope, debug, debug_on_panic},
};

#[cfg(feature = "arbitrary")]
pub(crate) use {
    arbitrary::{Arbitrary, Unstructured},
    crate::core::TmKind,
};

#[cfg(feature = "pretty-formatting")]
pub(crate) use std::cell::Cell;

