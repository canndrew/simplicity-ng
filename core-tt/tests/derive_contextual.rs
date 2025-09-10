#![feature(never_type)]

use {
    derive_where::derive_where,
    core_tt::{Contextual, Scheme, Ctx, Tm},
};

fn arbitrary_ctx<S: Scheme>() -> Ctx<S> {
    let ctx = Ctx::root();
    ctx.cons(&ctx.nat())
}

#[derive_where(Clone, PartialEq, Debug)]
#[derive(Contextual)]
#[scheme(S)]
pub struct OneField<S: Scheme> {
    term: Tm<S>,
}

#[test]
fn one_field_consistent() {
    let ctx = arbitrary_ctx::<!>();
    let val = OneField {
        term: ctx.nat_constant(3u32),
    };

    assert_eq!(val.ctx(), ctx);

    let (val_ctx, val_raw) = val.clone().into_raw();
    assert_eq!(val_ctx, ctx);

    let new_val = OneField::from_raw(val_ctx, val_raw);
    assert_eq!(new_val, val);
}

#[derive_where(Clone, PartialEq, Debug)]
#[derive(Contextual)]
#[scheme(S)]
pub struct TwoFields<S: Scheme> {
    term_0: Tm<S>,
    term_1: Tm<S>,
}

#[test]
fn two_fields_consistent() {
    let ctx = arbitrary_ctx::<!>();
    let val = TwoFields {
        term_0: ctx.nat_constant(3u32),
        term_1: ctx.nat_constant(5u32),
    };

    assert_eq!(val.ctx(), ctx);

    let (val_ctx, val_raw) = val.clone().into_raw();
    assert_eq!(val_ctx, ctx);

    let new_val = TwoFields::from_raw(val_ctx, val_raw);
    assert_eq!(new_val, val);
}

#[derive_where(Clone, PartialEq, Debug)]
#[derive(Contextual)]
#[scheme(S)]
pub struct TwoFieldsTuple<S: Scheme>(
    Tm<S>,
    Tm<S>,
);

#[test]
fn two_fields_tuple_consistent() {
    let ctx = arbitrary_ctx::<!>();
    let val = TwoFieldsTuple(
        ctx.nat_constant(3u32),
        ctx.nat_constant(5u32),
    );

    assert_eq!(val.ctx(), ctx);

    let (val_ctx, val_raw) = val.clone().into_raw();
    assert_eq!(val_ctx, ctx);

    let new_val = TwoFieldsTuple::from_raw(val_ctx, val_raw);
    assert_eq!(new_val, val);
}

#[derive_where(Clone, PartialEq, Debug)]
#[derive(Contextual)]
#[scheme(S)]
pub enum OneVariant<S: Scheme> {
    V0 {
        term: Tm<S>,
    },
}

#[test]
fn one_variant_consistent() {
    let ctx = arbitrary_ctx::<!>();
    let val = OneVariant::V0 {
        term: ctx.nat_constant(3u32),
    };

    assert_eq!(val.ctx(), ctx);

    let (val_ctx, val_raw) = val.clone().into_raw();
    assert_eq!(val_ctx, ctx);

    let new_val = OneVariant::from_raw(val_ctx, val_raw);
    assert_eq!(new_val, val);
}

#[derive_where(Clone, PartialEq, Debug)]
#[derive(Contextual)]
#[scheme(S)]
pub enum TwoVariants<S: Scheme> {
    V0 {
        term_0: Tm<S>,
        term_1: Tm<S>,
    },
    V1(
        Tm<S>,
    ),
}

#[test]
fn two_variants_consistent() {
    let ctx = arbitrary_ctx::<!>();
    let val = TwoVariants::V1(
        ctx.nat_constant(3u32),
    );

    assert_eq!(val.ctx(), ctx);

    let (val_ctx, val_raw) = val.clone().into_raw();
    assert_eq!(val_ctx, ctx);

    let new_val = TwoVariants::from_raw(val_ctx, val_raw);
    assert_eq!(new_val, val);
}

