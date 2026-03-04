#![recursion_limit = "300"]
#![feature(if_let_guard)]

mod priv_prelude;
mod tag;
mod infer_scope;
mod elab;
mod reduction;
mod simplify;
mod util;
mod type_list;

#[cfg(test)]
mod test;

pub use self::{
    tag::{
        Tag, MetavarTag, TagScheme,
        Ctx, Ty, Tm, Stuck, Scope, Name, TyKind, TmKind, StuckKind, NameKind, Iso,
    },
    infer_scope::InferScope,
    reduction::Reduction,
    elab::{ElabError, VarNames, CtxElabExt},
};

