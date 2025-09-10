pub(crate) use {
    std::{cmp, fmt},
    ext_trait::extension,
    core_tt::{
        Contextual, Scope, Scheme,
        Ctx, Ty, Tm, TmKind, TyKind,
    },
    more_tt::{Iso, TyExt as _, TmExt as _, ScopeTyExt as _},
    num::BigUint,
    derive_where::derive_where,
    crate::{
        //infer_scope::InferScope,
        //reduction::Reduction,
        reduction::ScopeReduction,
        util::as_equal,
    },
};

#[cfg(test)]
pub(crate) use {
    crate::infer_scope::{CtxInferExt, TyInferExt},
};
