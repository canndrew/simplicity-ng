use crate::priv_prelude::*;

/// A trait for types that can be stored under a [Scope].
///
/// # Deriving
///
/// This trait can be derived. You must the `#[scheme]` attribute to specify the [Scheme]. All
/// fields of the type must implement [Contextual]. You can use [NonContextual] to wrap arbitrary
/// data to be placed inside a type implementing [Contextual].
///
/// # Examples
///
/// Define a [Contextual] type which can be used with any [Scheme].
///
/// ```
/// # use core_tt::{Scheme, Contextual, NonContextual};
/// #[derive(Contextual)]
/// #[scheme(S)]
/// struct MyGenericType<S: Scheme> {
///     stuff: NonContextual<S, u32>,
/// }
/// ```
///
/// Define a [Contextual] type to be used with a specific [Scheme].
///
/// ```
/// # #![recursion_limit = "300"]
/// # use {
/// #     core_tt::{Scheme, Interner, Contextual, NonContextual},
/// #     lazy_static::lazy_static,
/// # };
/// # enum MyScheme {}
/// # impl Scheme for MyScheme {
/// #     type Tag = ();
/// #     fn interner() -> &'static Interner<MyScheme> {
/// #         lazy_static! {
/// #             static ref INTERNER: Interner<MyScheme> = Interner::new();
/// #         }
/// #         &*INTERNER
/// #     }
/// # }
/// #[derive(Contextual)]
/// #[scheme(MyScheme)]
/// struct MyType {
///     stuff: NonContextual<MyScheme, u32>,
/// }
/// ```
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
        let (old_ctx, raw) = self.clone().into_raw();
        let diff = ctx.len().strict_sub(old_ctx.len());
        assert_eq!(ctx.raw_ctx.nth_parent(diff), &old_ctx.raw_ctx);
        let raw = raw.weaken(diff);
        Self::from_raw(ctx.clone(), raw)
    }

    /*
    fn to_sigma_scoped(&self) -> Scope<S, Self>
    where
        Self: Sized + Clone,
    {
        let (ctx, raw) = self.clone().into_raw();
        let raw = raw.weaken(1);
        let raw_scope = RawScope::new(RawTy::unit(ctx.len()), raw);
        let raw_scope = ctx.raw_ctx.to_sigma_scope(raw_scope);
        Scope {
            raw_ctx: RawCtx::root(),
            raw_scope,
        }
    }
    */

    fn eliminates_var(&self, index: usize) -> bool;

    fn contains_subterm(&self, subterm: &RawTm<S>) -> bool;
}

#[derive_where(Clone; T: Clone)]
#[derive_where(PartialEq; T: PartialEq)]
#[derive_where(Eq; T: Eq)]
#[derive_where(PartialOrd; T: PartialOrd)]
#[derive_where(Ord; T: Ord)]
#[derive_where(Hash; T: hash::Hash)]
#[derive_where(Debug; T: fmt::Debug)]
pub struct NonContextual<S: Scheme, T> {
    pub(crate) raw_ctx: RawCtx<S>,
    pub(crate) val: T,
}

#[derive_where(Clone; T: Clone)]
#[derive_where(PartialEq; T: PartialEq)]
#[derive_where(Eq; T: Eq)]
#[derive_where(PartialOrd; T: PartialOrd)]
#[derive_where(Ord; T: Ord)]
#[derive_where(Hash; T: hash::Hash)]
#[derive_where(Debug; T: fmt::Debug)]
pub struct RawNonContextual<S: Scheme, T> {
    _ph: PhantomData<S>,
    val: T,
}

impl<S: Scheme, T> Contextual<S> for NonContextual<S, T>
where
    T: Clone + PartialEq + fmt::Debug,
{
    type Raw = RawNonContextual<S, T>;

    fn into_raw(self) -> (Ctx<S>, Weaken<RawNonContextual<S, T>>) {
        let NonContextual { raw_ctx, val } = self;
        let ctx = Ctx { raw_ctx };
        let usages = Usages::zeros(ctx.len());
        let weak = RawNonContextual { _ph: PhantomData, val };
        let raw = Weaken { usages, weak };
        (ctx, raw)
    }

    fn from_raw(ctx: Ctx<S>, raw: Weaken<RawNonContextual<S, T>>) -> NonContextual<S, T> {
        let Weaken { usages, weak } = raw;
        debug_assert!(usages.iter().all(|b| !b));
        let RawNonContextual { _ph, val } = weak;
        let Ctx { raw_ctx } = ctx;
        NonContextual { raw_ctx, val }
    }

    fn ctx(&self) -> Ctx<S> {
        Ctx { raw_ctx: self.raw_ctx.clone() }
    }

    fn eliminates_var(&self, _index: usize) -> bool {
        false
    }

    fn contains_subterm(&self, _subterm: &RawTm<S>) -> bool {
        false
    }
}

impl<S: Scheme, T> Substitute<S> for RawNonContextual<S, T>
where
    T: Clone + PartialEq + fmt::Debug,
{
    type RawSubstOutput = RawNonContextual<S, T>;

    fn to_subst_output(&self, _num_usages: usize) -> RawNonContextual<S, T> {
        self.clone()
    }

    fn subst(&self, filter: &Usages, _var_term: RawTm<S>) -> Weaken<RawNonContextual<S, T>> {
        let usages = Usages::zeros(filter.len().strict_sub(1));
        Weaken {
            usages,
            weak: self.clone(),
        }
    }

    fn eliminates_var(&self, _index: usize) -> bool {
        false
    }

    fn contains_subterm(&self, _subterm: RawTm<S>) -> bool {
        false
    }
}

impl<S: Scheme, T> NonContextual<S, T> {
    pub fn into_inner(self) -> T {
        self.val
    }

    pub fn inner_ref(&self) -> &T {
        &self.val
    }
}

pub trait BundleOfContextual<S: Scheme> {
    type Output;

    fn into_common_ctx(self) -> Self::Output;
}

macro_rules! impl_bundle_of_contextual_for_tuple (
    ($($name:ident,)*) => (
        impl<S: Scheme, $($name,)*> BundleOfContextual<S> for ($(&$name,)*)
        where
            $($name: Contextual<S> + Clone,)*
        {
            type Output = ($($name,)*);

            #[allow(unused_mut)]
            #[allow(unused_variables)]
            #[allow(unused_assignments)]
            #[allow(non_snake_case)]
            fn into_common_ctx(self) -> ($($name,)*) {
                let (ctx, ($($name,)*)) = BundleOfContextualRaw::<S>::into_common_ctx_raw(self);

                $(
                    let $name = $name::from_raw(ctx.clone(), $name);
                )*

                ($($name,)*)
            }
        }
    );
);

impl_bundle_of_contextual_for_tuple!();
impl_bundle_of_contextual_for_tuple!(T0,);
impl_bundle_of_contextual_for_tuple!(T0, T1,);
impl_bundle_of_contextual_for_tuple!(T0, T1, T2,);
impl_bundle_of_contextual_for_tuple!(T0, T1, T2, T3,);
impl_bundle_of_contextual_for_tuple!(T0, T1, T2, T3, T4,);
impl_bundle_of_contextual_for_tuple!(T0, T1, T2, T3, T4, T5,);
impl_bundle_of_contextual_for_tuple!(T0, T1, T2, T3, T4, T5, T6,);
impl_bundle_of_contextual_for_tuple!(T0, T1, T2, T3, T4, T5, T6, T7,);

impl<const LEN: usize, S: Scheme, T> BundleOfContextual<S> for [&T; LEN]
where
    T: Contextual<S> + Clone,
{
    type Output = [T; LEN];

    fn into_common_ctx(self) -> [T; LEN] {
        let (ctx, things_raw) = BundleOfContextualRaw::<S>::into_common_ctx_raw(self);

        things_raw.map(|thing_raw| T::from_raw(ctx.clone(), thing_raw))
    }
}


