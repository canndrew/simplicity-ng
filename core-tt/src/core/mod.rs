mod contextual;
mod ctx;
mod ty;
mod term;
mod stuck;
mod scope;
mod nat;
//mod pack;

pub use self::{
    contextual::{Contextual, DummyContextual},
    ctx::Ctx,
    ty::{Ty, TyKind},
    term::{Tm, TmKind},
    stuck::{Stuck, StuckKind},
    scope::Scope,
    nat::{Nat, NatKind},
    //pack::{ContextualTuple, Pack},
};

/*
pub struct Parts<N: Name, const ARITY: usize, P: Tuple<N, ARITY>> {
    raw_ctx: RawCtx<N>,
    raw_parts: RawParts<N, ARITY, P::TupleRaw>,
}
*/

