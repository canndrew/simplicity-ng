#![recursion_limit = "300"]
#![feature(never_type)]

mod priv_prelude;

#[macro_export]
macro_rules! same_ctx_impl (
    ($([$name:ident $($t:tt)?],)*) => (
        let ($($name,)*) = Ctx::into_common_ctx(($($($t)? $name,)*));
    );
);

#[macro_export]
macro_rules! same_ctx (
    ($($($t0:tt $($t1:ident)?),+ $(,)*)?) => (
        same_ctx_impl!($($([$($t1)? $t0],)+)?)
    );
);

mod util;
mod scheme;
mod ctx;
pub mod closed;
mod ty;
mod term;
mod stuck;
mod scope;

mod uninhabited;
mod contractible;
mod iso;
mod epi;
mod inj;
mod equiprovable;

#[cfg(test)]
mod test;

pub use self::{
    scheme::{Scheme, SchemeExt},
    ctx::CtxExt,
    ty::TyExt,
    term::TmExt,
    stuck::StuckExt,
    scope::{ScopeTmExt, ScopeTyExt},
    uninhabited::Uninhabited,
    contractible::Contractible,
    iso::Iso,
    epi::{Epi, ScopeEpiExt},
    inj::Inj,
    equiprovable::Equiprovable,
};

