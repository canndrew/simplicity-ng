#![feature(never_type)]

type Ctx = core_tt::Ctx<!>;
type Tm = core_tt::Tm<!>;

#[test]
fn subst_zero() {
    let ctx = Ctx::root();
    let scope = ctx.nat().scope(|x| x.ctx().zero());
    let output = scope.bind(&ctx.nat_constant(23u32));
    let expected = ctx.zero();
    assert_eq!(output, expected);
}

#[test]
fn subst_add_mul() {
    let ctx = Ctx::root();
    ctx.with_cons(&ctx.nat(), |x| {
        let scope = x.ctx().nat().scope(|y| {
            Tm::add(
                &y.ctx().nat_constant(3u32),
                &Tm::mul(
                    &x,
                    &Tm::add(&y, &y.ctx().nat_constant(1u32)),
                ),
            )
        });
        let output = scope.bind(&Tm::add(&x, &x.ctx().nat_constant(2u32)));
        let expected = Tm::add(
            &Tm::mul(
                &x.ctx().nat_constant(3u32),
                &Tm::add(&x, &x.ctx().nat_constant(1u32)),
            ),
            &Tm::mul(&x, &x),
        );
        assert_eq!(output, expected);
    });
}

