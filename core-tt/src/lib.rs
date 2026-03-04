#![recursion_limit = "300"]
#![feature(try_trait_v2)]
#![feature(try_trait_v2_residual)]
#![feature(never_type)]
#![feature(mapped_lock_guards)]

mod priv_prelude;
mod scheme;
mod raw;
mod core;
mod non_zero_big_uint;
mod usages;
#[macro_use]
mod util;
mod intern;

#[cfg(feature = "arbitrary")]
pub mod arbitrary;

#[cfg(feature = "pretty-formatting")]
mod pprint;

#[cfg(test)]
mod test;

#[cfg(debug_assertions)]
mod sanity_check;

pub use {
    crate::{
        scheme::Scheme,
        usages::Usages,
        intern::Interner,
        core::{
            Contextual, BundleOfContextual, Ctx,
            NonContextual,
            Ty, Tm, Stuck,
            TyKind, TmKind, StuckKind,
            Scope,
            Nat, NatKind,
            Name, NameKind,
        },
        non_zero_big_uint::NonZeroBigUint,
    },
    num::BigUint,
};

#[doc(hidden)]
pub use crate::raw::{
    Weaken, Substitute, RawTm,
};

pub use core_tt_macros::Contextual;

