#![feature(never_type)]

//use core_tt::{assert_let, Contextual};
use core_tt::Contextual;

macro_rules! assert_let (
    ($pat:pat = $expr:expr) => {
        let $pat = $expr else { unreachable!() };
    };
);

type Ctx = core_tt::Ctx<!>;
//type Tm = core_tt::Tm<!>;
type Ty = core_tt::Ty<!>;
type TmKind = core_tt::TmKind<!>;
type TyKind = core_tt::TyKind<!>;
type StuckKind = core_tt::StuckKind<!>;

#[test]
fn eta_unit() {
    let ctx = Ctx::root();
    ctx.unit_ty().with_cons(|x| {
        assert_let!(TmKind::Unit = x.kind());
    });
}

#[test]
fn eta_pair() {
    let ctx = Ctx::root();
    let sigma_ty = ctx.unit_ty().sigma(|x| x.ctx().unit_ty());
    sigma_ty.with_cons(|pair| {
        assert_let!(TmKind::Pair { tail_ty, head_term, tail_term } = pair.kind());
        tail_ty.map_out(|head_term, tail_ty| {
            assert_let!(TmKind::Unit = head_term.kind());
            assert_let!(TyKind::Unit = tail_ty.kind());
        });
        assert_let!(TmKind::Unit = head_term.kind());
        assert_let!(TmKind::Unit = tail_term.kind());
    });
}

#[test]
fn eta_func() {
    let ctx = Ctx::root();
    let pi_ty = ctx.nat().pi(|x| x.ctx().unit_ty());
    pi_ty.with_cons(|func| {
        assert_let!(TmKind::Func { res_term } = func.kind());
        res_term.map_out(|_, res_term| {
            assert_let!(TmKind::Unit = res_term.kind());
        });
    });
}

#[test]
fn eta_cong() {
    let ctx = Ctx::root();
    let cong_ty = {
        ctx
        .universe()
        .sigma(|ty| {
            ty
            .to_ty()
            .sigma(|x0| {
                ty
                .to_ty()
                .weaken_into(&x0.ctx())
                .sigma(|x1| {
                    x0
                    .equals(&x1)
                    .sigma(|eq| {
                        eq
                        .cong(
                            |_, _, elim| elim.ctx().universe(),
                            |ty| ty.ctx().unit_ty().to_term(),
                        )
                        .to_ty()
                    })
                })
            })
        })
    };
    cong_ty.with_cons(|sigma| {
        let cong_term = sigma.proj_tail().proj_tail().proj_tail().proj_tail();
        assert_let!(TmKind::Stuck { stuck } = cong_term.kind());
        assert_let!(StuckKind::Cong { elim, motive, inhab } = stuck.kind());
        assert_let!(StuckKind::ProjHead { elim } = elim.kind());
        assert_let!(StuckKind::ProjTail { elim } = elim.kind());
        assert_let!(StuckKind::ProjTail { elim } = elim.kind());
        assert_let!(StuckKind::ProjTail { elim } = elim.kind());
        assert_let!(StuckKind::Var { index: 0 } = elim.kind());
        motive.map_out(|_, motive| {
            motive.map_out(|_, motive| {
                motive.map_out(|_, motive| {
                    assert_let!(TyKind::Stuck { stuck } = motive.kind());
                    assert_let!(StuckKind::Cong { elim, motive, inhab } = stuck.kind());
                    assert_let!(StuckKind::Var { index: 3 } = elim.kind());
                    motive.map_out(|_, motive| {
                        motive.map_out(|_, motive| {
                            motive.map_out(|_, motive| {
                                assert_let!(TyKind::Universe = motive.kind());
                            });
                        });
                    });
                    inhab.map_out(|_, inhab| {
                        assert_let!(TmKind::Type { ty } = inhab.kind());
                        assert_let!(TyKind::Unit = ty.kind());
                    });
                });
            });
        });
        inhab.map_out(|_, inhab| {
            assert_let!(TmKind::Unit = inhab.kind());
        });
    });
}

#[test]
fn eta_unique_identity() {
    let ctx = Ctx::root();
    let unique_identity_ty = {
        ctx
        .universe()
        .sigma(|ty| {
            ty
            .to_ty()
            .sigma(|x| {
                x
                .equals(&x)
                .sigma(|eq| {
                    eq
                    .unique_identity(
                        |_, elim| elim.ctx().universe(),
                        |ty| ty.ctx().unit_ty().to_term(),
                    )
                    .to_ty()
                })
            })
        })
    };
    unique_identity_ty.with_cons(|sigma| {
        let unique_identity_term = sigma.proj_tail().proj_tail().proj_tail();
        assert_let!(TmKind::Stuck { stuck } = unique_identity_term.kind());
        assert_let!(StuckKind::UniqueIdentity { elim, motive, inhab } = stuck.kind());
        assert_let!(StuckKind::ProjHead { elim } = elim.kind());
        assert_let!(StuckKind::ProjTail { elim } = elim.kind());
        assert_let!(StuckKind::ProjTail { elim } = elim.kind());
        assert_let!(StuckKind::Var { index: 0 } = elim.kind());
        motive.map_out(|_, motive| {
            motive.map_out(|_, motive| {
                assert_let!(TyKind::Stuck { stuck } = motive.kind());
                assert_let!(StuckKind::UniqueIdentity { elim, motive, inhab } = stuck.kind());
                assert_let!(StuckKind::Var { index: 2 } = elim.kind());
                motive.map_out(|_, motive| {
                    motive.map_out(|_, motive| {
                        assert_let!(TyKind::Universe = motive.kind());
                    });
                });
                inhab.map_out(|_, inhab| {
                    assert_let!(TmKind::Type { ty } = inhab.kind());
                    assert_let!(TyKind::Unit = ty.kind());
                });
            });
        });
        inhab.map_out(|_, inhab| {
            assert_let!(TmKind::Unit = inhab.kind());
        });
    });
}

#[test]
fn eta_explode() {
    let ctx = Ctx::root();
    let explode_ty = ctx.never().sigma(|x| {
        x.explode(|elim| elim.ctx().universe()).to_ty()
    });
    explode_ty.with_cons(|pair| {
        let explode_term = pair.proj_tail();
        assert_let!(TmKind::Stuck { stuck } = explode_term.kind());
        assert_let!(StuckKind::Explode { elim, motive } = stuck.kind());
        assert_let!(StuckKind::ProjHead { elim } = elim.kind());
        assert_let!(StuckKind::Var { index: 0 } = elim.kind());
        motive.map_out(|_, motive| {
            assert_let!(TyKind::Stuck { stuck } = motive.kind());
            assert_let!(StuckKind::Explode { elim, motive } = stuck.kind());
            assert_let!(StuckKind::Var { index: 1 } = elim.kind());
            motive.map_out(|_, motive| {
                assert_let!(TyKind::Universe = motive.kind());
            });
        });
    });
}

#[test]
fn eta_case() {
    let ctx = Ctx::root();
    let case_ty = {
        ctx.universe().sigma(|lhs_ty| {
            let lhs_ty = lhs_ty.to_ty();
            lhs_ty.ctx().universe().sigma(|rhs_ty| {
                let rhs_ty = rhs_ty.to_ty();
                Ty::sum(&lhs_ty, &rhs_ty).sigma(|sum| {
                    sum
                    .case(
                        |elim| elim.ctx().universe(),
                        |lhs_term| lhs_term.ctx().unit_ty().to_term(),
                        |rhs_term| {
                            rhs_term
                            .ctx()
                            .unit_ty()
                            .sigma(|unit| unit.ctx().unit_ty())
                            .to_term()
                        },
                    )
                    .to_ty()
                })
            })
        })
    };
    case_ty.with_cons(|sigma| {
        let case_term = sigma.proj_tail().proj_tail().proj_tail();
        assert_let!(TmKind::Stuck { stuck } = case_term.kind());
        assert_let!(StuckKind::Case { elim, motive, lhs_inhab, rhs_inhab } = stuck.kind());
        assert_let!(StuckKind::ProjHead { elim } = elim.kind());
        assert_let!(StuckKind::ProjTail { elim } = elim.kind());
        assert_let!(StuckKind::ProjTail { elim } = elim.kind());
        assert_let!(StuckKind::Var { index: 0 } = elim.kind());
        motive.map_out(|_, motive| {
            assert_let!(TyKind::Stuck { stuck } = motive.kind());
            assert_let!(StuckKind::Case { elim, motive, lhs_inhab, rhs_inhab } = stuck.kind());
            assert_let!(StuckKind::Var { index: 1 } = elim.kind());
            motive.map_out(|_, motive| {
                assert_let!(TyKind::Universe = motive.kind());
            });
            lhs_inhab.map_out(|_, lhs_inhab| {
                assert_let!(TmKind::Type { ty } = lhs_inhab.kind());
                assert_let!(TyKind::Unit = ty.kind());
            });
            rhs_inhab.map_out(|_, rhs_inhab| {
                assert_let!(TmKind::Type { ty } = rhs_inhab.kind());
                assert_let!(TyKind::Sigma { tail_ty } = ty.kind());
                tail_ty.map_out(|head_term, tail_ty| {
                    assert_let!(TmKind::Unit = head_term.kind());
                    assert_let!(TyKind::Unit = tail_ty.kind());
                });
            });
        });
        lhs_inhab.map_out(|_, lhs_inhab| {
            assert_let!(TmKind::Unit = lhs_inhab.kind());
        });
        rhs_inhab.map_out(|_, rhs_inhab| {
            assert_let!(TmKind::Pair { tail_ty, head_term, tail_term } = rhs_inhab.kind());
            tail_ty.map_out(|head_term, tail_ty| {
                assert_let!(TmKind::Unit = head_term.kind());
                assert_let!(TyKind::Unit = tail_ty.kind());
            });
            assert_let!(TmKind::Unit = head_term.kind());
            assert_let!(TmKind::Unit = tail_term.kind());
        });
    });
}

