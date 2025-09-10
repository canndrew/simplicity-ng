use crate::priv_prelude::*;

pub trait Contextual<S: Scheme> {
    type Raw: Substitute<S, RawSubstOutput = Self::Raw> + Clone + PartialEq + fmt::Debug;

    fn into_raw(self) -> (Ctx<S>, Weaken<Self::Raw>);
    fn from_raw(ctx: Ctx<S>, raw: Weaken<Self::Raw>) -> Self;

    fn ctx(&self) -> Ctx<S>;

    fn try_strengthen_to_index(&self, index: usize) -> Option<Self>
    where
        Self: Sized + Clone,
    {
        let (ctx, raw) = self.clone().into_raw();
        let diff = ctx.len().strict_sub(index);
        let raw = raw.try_strengthen_to_index(index)?;
        let raw_ctx = ctx.raw_ctx.nth_parent(diff).clone();
        let ctx = Ctx { raw_ctx };
        Some(Self::from_raw(ctx, raw))
    }

    fn weaken_into(&self, ctx: &Ctx<S>) -> Self
    where
        Self: Sized + Clone,
    {
        let (old_ctx, mut raw) = self.clone().into_raw();
        let diff = ctx.len().strict_sub(old_ctx.len());
        assert_eq!(ctx.raw_ctx.nth_parent(diff), &old_ctx.raw_ctx);
        raw.weaken(diff);
        Self::from_raw(ctx.clone(), raw)
    }

    fn to_sigma_scoped(&self) -> Scope<S, Self>
    where
        Self: Sized + Clone,
    {
        let (ctx, mut raw) = self.clone().into_raw();
        raw.weaken(1);
        let raw_scope = RawScope::new(RawTy::unit(ctx.len()), raw);
        let raw_scope = ctx.raw_ctx.to_sigma_scope(raw_scope);
        Scope {
            raw_ctx: RawCtx::root(),
            raw_scope,
        }
    }

    fn eliminates_var(&self, index: usize) -> bool;
}

#[derive_where(Clone, PartialEq, Eq, Hash, Debug)]
pub struct DummyContextual<S: Scheme> {
    raw_ctx: RawCtx<S>,
}

#[derive_where(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Copy)]
pub struct RawDummyContextual<S: Scheme> {
    _ph: PhantomData<S>,
}

impl<S: Scheme> Contextual<S> for DummyContextual<S> {
    type Raw = RawDummyContextual<S>;

    fn into_raw(self) -> (Ctx<S>, Weaken<RawDummyContextual<S>>) {
        let DummyContextual { raw_ctx } = self;
        let ctx = Ctx { raw_ctx };
        let usages = Usages::zeros(ctx.len());
        let weak = RawDummyContextual { _ph: PhantomData };
        let raw = Weaken { usages, weak };
        (ctx, raw)
    }

    fn from_raw(ctx: Ctx<S>, raw: Weaken<RawDummyContextual<S>>) -> DummyContextual<S> {
        let Weaken { usages, weak } = raw;
        debug_assert!(usages.iter().all(|b| !b));
        let RawDummyContextual { _ph } = weak;
        let Ctx { raw_ctx } = ctx;
        DummyContextual { raw_ctx }
    }

    fn ctx(&self) -> Ctx<S> {
        Ctx { raw_ctx: self.raw_ctx.clone() }
    }

    fn eliminates_var(&self, _index: usize) -> bool {
        false
    }
}

impl<S: Scheme> Substitute<S> for RawDummyContextual<S> {
    type RawSubstOutput = RawDummyContextual<S>;

    fn to_subst_output(&self, _num_usages: usize) -> RawDummyContextual<S> {
        *self
    }

    fn subst(&self, filter: &Usages, _var_term: RawTm<S>) -> Weaken<RawDummyContextual<S>> {
        let usages = Usages::zeros(filter.len().strict_sub(1));
        Weaken {
            usages,
            weak: *self,
        }
    }

    fn eliminates_var(&self, _index: usize) -> bool {
        false
    }
}

