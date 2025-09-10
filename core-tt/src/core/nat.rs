use crate::priv_prelude::*;

pub struct Nat<S: Scheme> {
    pub(crate) raw_ctx: RawCtx<S>,
    pub(crate) raw_nat: RawNat<S>,
}

pub struct NatKind<S: Scheme> {
    pub succs_count: BigUint,
    pub stuck_opt: Option<Stuck<S>>,
}

impl<S: Scheme> Nat<S> {
    pub fn ctx(&self) -> Ctx<S> {
        Ctx {
            raw_ctx: self.raw_ctx.clone(),
        }
    }

    pub fn kind(&self) -> NatKind<S> {
        let succs_count = self.raw_nat.succs_count();
        let remaining = self.raw_nat.strict_sub_constant(&succs_count);
        let stuck_opt = if remaining.is_zero() {
            None
        } else {
            let raw_stuck = RawStuck::nat(remaining);
            let raw_typed_stuck = RawTyped::from_parts(RawTy::nat(self.raw_ctx.len()), raw_stuck);
            let stuck = Stuck { raw_ctx: self.raw_ctx.clone(), raw_typed_stuck };
            Some(stuck)
        };
        NatKind { succs_count, stuck_opt }
    }

    pub fn to_term(&self) -> Tm<S> {
        let Nat { raw_ctx, raw_nat } = self;
        let raw_term = raw_nat.clone().into_raw_term();
        let raw_typed_term = RawTyped::from_parts(RawTy::nat(raw_ctx.len()), raw_term);
        Tm { raw_ctx: raw_ctx.clone(), raw_typed_term }
    }

    pub fn succs(&self, count: &NonZeroBigUint) -> Nat<S> {
        let Nat { raw_ctx, raw_nat } = self;
        let raw_ctx = raw_ctx.clone();
        let raw_nat = raw_nat.clone().succs(count);
        Nat { raw_ctx, raw_nat }
    }
}

