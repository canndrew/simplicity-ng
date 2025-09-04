mod priv_prelude;
mod core;
mod name;
mod typecheck;

pub use self::{
    typecheck::CheckError,
    core::{Ctx, Ty, Tm, Scope},
};

