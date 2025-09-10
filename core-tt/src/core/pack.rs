use crate::priv_prelude::*;

pub trait ContextualTuple<S: Scheme, const ARITY: usize> {
    type RawTuple:
            RawContextualTuple<S, ARITY>
            + SubstituteTuple<S, ARITY, RawTupleSubstOutput = Self::RawTuple>
            + Clone + PartialEq + fmt::Debug;
    /*
    type TupleMappedScheme<V: Scheme>:
            ContextualTuple<
                V, ARITY,
                RawTuple = <Self::RawTuple as RawContextualTuple<S, ARITY>>::RawTupleMappedScheme<V>,
            >
            + Clone + PartialEq;
    */

    fn merge_ctx(self) -> (RawCtx<S>, Self::RawTuple);
    fn from_raw_tuple(ctx: Ctx<S>, raw_tuple: Self::RawTuple) -> Self;
}

macro_rules! impl_contextual_tuple {
    ($($ty:ident,)*) => {
        impl<S: Scheme, $($ty,)*> ContextualTuple<S, {count_tokens!($($ty)*)}> for ($($ty,)*)
        where
            $($ty: Contextual<S>,)*
        {
            type RawTuple = ($($ty::Raw,)*);
            //type TupleMappedScheme<V: Scheme> = ($($ty::MappedScheme<V>,)*);

            #[allow(unused)]
            #[allow(non_snake_case)]
            fn merge_ctx(self) -> (RawCtx<S>, ($($ty::Raw,)*)) {
                let mut max_raw_ctx = RawCtx::root();
                let mut max_ctx_len = 0;

                let ($($ty,)*) = self;
                $(
                    let ctx_len = $ty.ctx().len();
                    if ctx_len > max_ctx_len {
                        max_ctx_len = ctx_len;
                        max_raw_ctx = $ty.ctx().raw_ctx;
                    }
                )*
                $(
                    let $ty = {
                        let (ctx, mut raw) = $ty.into_raw();
                        let ctx_len = ctx.len();
                        let diff = max_ctx_len.strict_sub(ctx_len);
                        assert_eq!(max_raw_ctx.nth_parent(diff), &ctx.raw_ctx);
                        raw.weaken(diff);
                        raw
                    };
                )*
                (max_raw_ctx, ($($ty,)*))
            }

            #[allow(unused)]
            #[allow(non_snake_case)]
            fn from_raw_tuple(ctx: Ctx<S>, raw_tuple: ($($ty::Raw,)*)) -> ($($ty,)*) {
                let ($($ty,)*) = raw_tuple;
                ($(Contextual::from_raw(ctx.clone(), $ty),)*)
            }
        }
    };
}

impl_contextual_tuple!();
impl_contextual_tuple!(T0,);
impl_contextual_tuple!(T0,T1,);
impl_contextual_tuple!(T0,T1,T2,);
impl_contextual_tuple!(T0,T1,T2,T3,);
impl_contextual_tuple!(T0,T1,T2,T3,T4,);
impl_contextual_tuple!(T0,T1,T2,T3,T4,T5,);
impl_contextual_tuple!(T0,T1,T2,T3,T4,T5,T6,);
impl_contextual_tuple!(T0,T1,T2,T3,T4,T5,T6,T7,);

pub struct Pack<S: Scheme, const ARITY: usize, T: ContextualTuple<S, ARITY>> {
    raw_ctx: RawCtx<S>,
    raw_pack: RawPack<S, ARITY, T::RawTuple>,
}

impl<S: Scheme, const ARITY: usize, T: ContextualTuple<S, ARITY> + Clone> Clone for Pack<S, ARITY, T> {
    fn clone(&self) -> Pack<S, ARITY, T> {
        Pack {
            raw_ctx: self.raw_ctx.clone(),
            raw_pack: self.raw_pack.clone(),
        }
    }
}

impl<S: Scheme, const ARITY: usize, T: ContextualTuple<S, ARITY> + PartialEq> PartialEq for Pack<S, ARITY, T> {
    fn eq(&self, other: &Pack<S, ARITY, T>) -> bool {
        self.raw_ctx == other.raw_ctx && self.raw_pack == other.raw_pack
    }
}

impl<S, const ARITY: usize, T> Pack<S, ARITY, T>
where
    S: Scheme,
    T: ContextualTuple<S, ARITY>,
{
    pub fn from_tuple(tuple: T) -> Pack<S, ARITY, T> {
        let (raw_ctx, raw_tuple) = tuple.merge_ctx();
        let raw_pack = RawPack::from_tuple(raw_tuple);
        Pack { raw_ctx, raw_pack }
    }

    pub fn into_tuple(self) -> T {
        let Pack { raw_ctx, raw_pack } = self;
        let ctx = Ctx { raw_ctx };
        let raw_tuple = raw_pack.into_tuple();
        T::from_raw_tuple(ctx, raw_tuple)
    }

    /*
    pub fn map_scheme<V: Scheme>(
        &self,
        map_user_ty: impl FnMut(&S::UserTy) -> V::UserTy,
        map_user_term: impl FnMut(&S::UserTm) -> V::UserTm,
    ) -> Pack<V, ARITY, T::TupleMappedScheme<V>> {
        let mut map_user_ty = map_user_ty;
        let mut map_user_term = map_user_term;

        let Pack { raw_ctx, raw_pack } = self;
        let raw_ctx = raw_ctx.map_scheme(&mut map_user_ty, &mut map_user_term);
        let raw_pack = raw_pack.map_scheme(&mut map_user_ty, &mut map_user_term);
        Pack { raw_ctx, raw_pack }
    }
    */
}

impl<S, const ARITY: usize, T> Contextual<S> for Pack<S, ARITY, T>
where
    S: Scheme,
    T: ContextualTuple<S, ARITY>,
{
    type Raw = RawPack<S, ARITY, T::RawTuple>;
    //type MappedScheme<V: Scheme> = Pack<V, ARITY, T::TupleMappedScheme<V>>;

    /*
    fn raw_ctx(&self) -> &RawCtx<S> {
        &self.raw_ctx
    }

    fn raw(&self) -> &RawPack<S, ARITY, T::RawTuple> {
        &self.raw_pack
    }
    */

    fn into_raw(self) -> (Ctx<S>, RawPack<S, ARITY, T::RawTuple>) {
        let Pack { raw_ctx, raw_pack } = self;
        let ctx = Ctx { raw_ctx };
        (ctx, raw_pack)
    }

    fn from_raw(ctx: Ctx<S>, raw: RawPack<S, ARITY, T::RawTuple>) -> Pack<S, ARITY, T> {
        Pack { raw_ctx: ctx.raw_ctx, raw_pack: raw }
    }

    fn ctx(&self) -> Ctx<S> {
        let raw_ctx = self.raw_ctx.clone();
        Ctx { raw_ctx }
    }
}

