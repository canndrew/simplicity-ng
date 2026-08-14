#![recursion_limit = "300"]

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

use ::core::convert::Infallible;
use ::core::ops::ControlFlow;

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

/// Limited form of the `Try` trait that just allows mapping the "Ok" type.
pub trait MyTry {
    type Output;
    type Residual;
    type AltOutput<U>: MyTry<Output = U, Residual = Self::Residual>;

    fn from_output(output: Self::Output) -> Self;
    fn from_residual(res: Self::Residual) -> Self;
    fn branch(self) -> ControlFlow<Self::Residual, Self::Output>;
}

impl<T> MyTry for Option<T> {
    type Output = T;
    type Residual = Option<Infallible>;
    type AltOutput<U> = Option<U>;

    fn from_output(output: Self::Output) -> Self { Some(output) }
    fn from_residual(_: Self::Residual) -> Self { None }
    fn branch(self) -> ControlFlow<Self::Residual, Self::Output> {
        match self {
            Some(inn) => ControlFlow::Continue(inn),
            None => ControlFlow::Break(None),
        }
    }
}

impl<T, E> MyTry for Result<T, E> {
    type Output = T;
    type Residual = Result<Infallible, E>;
    type AltOutput<U> = Result<U, E>;

    fn from_output(output: Self::Output) -> Self { Ok(output) }
    fn from_residual(res: Self::Residual) -> Self { res.map(|infallible| match infallible {}) }
    fn branch(self) -> ControlFlow<Self::Residual, Self::Output> {
        match self {
            Ok(inn) => ControlFlow::Continue(inn),
            Err(err) => ControlFlow::Break(Err(err)),
        }
    }
}

