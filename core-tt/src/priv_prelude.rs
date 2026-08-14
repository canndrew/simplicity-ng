pub(crate) use crate::MyTry;

pub(crate) use {
    std::{
        cmp, fmt, hash, iter, ops, mem,
        marker::PhantomData,
        ops::ControlFlow,
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
        core::{
            Contextual, NonContextual, BundleOfContextual,
            Ctx, Ty, Tm, Stuck, Scope, Name,
        },
        usages::Usages,
        non_zero_big_uint::NonZeroBigUint,
        raw::{
            BundleOfContextualRaw, merge_ctxs,
            Substitute, Weaken, RawCtx, RawCtxCons, RawTy, RawTm, RawStuck, RawScope, RawScopeKind,
            RawTyKind, RawTmKind, RawStuckKind, RawTyped, RawTypedKind,
            raw_scope, raw_scope_2, raw_scope_3, try_raw_scope,
            RawNat, MaxAll, AddAll, MulAll,
            RawName, RawNameKind,
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
pub(crate) use arbitrary::{Arbitrary, Unstructured};

#[cfg(any(doc, feature = "arbitrary"))]
pub(crate) use crate::core::{TyKind, TmKind};

#[cfg(feature = "pretty-formatting")]
pub(crate) use std::cell::Cell;

