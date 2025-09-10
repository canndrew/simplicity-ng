#![feature(never_type)]

mod priv_prelude;
mod infer_scope;
mod reduction;
mod util;

pub use crate::infer_scope::{
    InferScope, ScopeInferExt, TyInferExt, CtxInferExt, ContextualInferExt,
};

#[cfg(test)]
mod test;

