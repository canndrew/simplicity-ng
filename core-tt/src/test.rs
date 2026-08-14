use core::convert::Infallible;
use crate::priv_prelude::*;

#[test]
fn ty_to_term_to_ty() {
    let ctx: Ctx<Infallible> = Ctx::root();
    
    ctx
    .universe()
    .with_cons(|ty| {
        assert_eq!(ty.to_ty().to_term(), ty);
    });
    
    let ty = ctx.unit_ty();
    assert_eq!(ty.to_term().to_ty(), ty);
}

#[test]
fn cong_beta() {
    let ctx: Ctx<Infallible> = Ctx::root();

    ctx
    .with_names(|[eq_name_0, eq_name_1, elim_name, eq_name]| {
        eq_name
        .ctx()
        .universe()
        .with_cons(|ty| {
            let ty = ty.to_ty();
            let motive_ty = {
                ty
                .pi(&eq_name_0, |eq_term_0| {
                    let ctx = eq_term_0.ctx();
                    ty
                    .weaken_into(&ctx)
                    .pi(&eq_name_1, |eq_term_1| {
                        eq_term_0
                        .equals(&eq_term_1)
                        .pi(&elim_name, |elim| {
                            elim.ctx().universe()
                        })
                    })
                })
            };
            motive_ty
            .with_cons(|motive| {
                let ctx = motive.ctx();
                let inhab_ty = {
                    ty
                    .weaken_into(&ctx)
                    .pi(&eq_name, |eq_term| {
                        motive
                        .app(&eq_term)
                        .app(&eq_term)
                        .app(&eq_term.refl())
                        .to_ty()
                    })
                };
                inhab_ty
                .with_cons(|inhab| {
                    ty
                    .weaken_into(&inhab.ctx())
                    .with_cons(|eq_term| {
                        let expected = inhab.app(&eq_term);
                        let got = {
                            eq_term
                            .refl()
                            .cong(
                                |eq_term_0, eq_term_1, elim| {
                                    motive
                                    .app(&eq_term_0)
                                    .app(&eq_term_1)
                                    .app(&elim)
                                    .to_ty()
                                },
                                |eq_term| {
                                    inhab.app(&eq_term)
                                },
                            )
                        };
                        assert_eq!(expected, got);
                    })
                })
            })
        })
    });
}

#[test]
fn unique_identity_beta() {
    let ctx: Ctx<Infallible> = Ctx::root();

    ctx
    .with_names(|[eq_name, elim_name]| {
        elim_name
        .ctx()
        .universe()
        .with_cons(|ty| {
            let ty = ty.to_ty();
            let motive_ty = {
                ty
                .pi(&eq_name, |eq_term| {
                    eq_term
                    .equals(&eq_term)
                    .pi(&elim_name, |elim| {
                        elim.ctx().universe()
                    })
                })
            };
            motive_ty
            .with_cons(|motive| {
                let ctx = motive.ctx();
                let inhab_ty = {
                    ty
                    .weaken_into(&ctx)
                    .pi(&eq_name, |eq_term| {
                        motive
                        .app(&eq_term)
                        .app(&eq_term.refl())
                        .to_ty()
                    })
                };
                inhab_ty
                .with_cons(|inhab| {
                    ty
                    .weaken_into(&inhab.ctx())
                    .with_cons(|eq_term| {
                        let expected = inhab.app(&eq_term);
                        let got = {
                            eq_term
                            .refl()
                            .unique_identity(
                                |eq_term, elim| {
                                    motive
                                    .app(&eq_term)
                                    .app(&elim)
                                    .to_ty()
                                },
                                |eq_term| {
                                    inhab.app(&eq_term)
                                },
                            )
                        };
                        assert_eq!(expected, got);
                    })
                })
            })
        })
    });
}

#[test]
fn unit_eta() {
    let ctx: Ctx<Infallible> = Ctx::root();
    ctx
    .unit_ty()
    .with_cons(|unit_term| {
        let expected = unit_term.ctx().unit_term();
        assert_eq!(expected, unit_term);
    })
}

#[test]
fn case_beta() {
    let ctx: Ctx<Infallible> = Ctx::root();

    ctx
    .with_names(|[lhs_name, elim_name, lhs_elim_name, rhs_elim_name]| {
        rhs_elim_name
        .ctx()
        .universe()
        .with_cons(|lhs_ty| {
            let lhs_ty = lhs_ty.to_ty();

            lhs_ty
            .ctx()
            .universe()
            .with_cons(|rhs_ty| {
                let rhs_ty = rhs_ty.to_ty();
                let sum_ty = lhs_ty.sum(&lhs_name, &rhs_ty);
                let motive_ty = {
                    sum_ty
                    .pi(&elim_name, |elim| {
                        elim.ctx().universe()
                    })
                };
                motive_ty
                .with_cons(|motive| {
                    let ctx = motive.ctx();
                    let lhs_inhab_ty = {
                        lhs_ty
                        .weaken_into(&ctx)
                        .pi(&lhs_elim_name, |lhs_term| {
                            motive.app(&lhs_term.inj_lhs(&lhs_name, &rhs_ty)).to_ty()
                        })
                    };
                    lhs_inhab_ty
                    .with_cons(|lhs_inhab| {
                        let ctx = lhs_inhab.ctx();
                        let rhs_inhab_ty = {
                            rhs_ty
                            .weaken_into(&ctx)
                            .pi(&rhs_elim_name, |rhs_term| {
                                motive.app(&rhs_term.inj_rhs(&lhs_name, &lhs_ty)).to_ty()
                            })
                        };
                        rhs_inhab_ty
                        .with_cons(|rhs_inhab| {
                            let ctx = rhs_inhab.ctx();
                            lhs_ty
                            .weaken_into(&ctx)
                            .with_cons(|lhs_term| {
                                let expected = lhs_inhab.app(&lhs_term);
                                let got = {
                                    lhs_term
                                    .inj_lhs(&lhs_name, &rhs_ty)
                                    .case(
                                        |elim| motive.app(&elim).to_ty(),
                                        |lhs_term| lhs_inhab.app(&lhs_term),
                                        |rhs_term| rhs_inhab.app(&rhs_term),
                                    )
                                };
                                assert_eq!(expected, got);
                            });
                            rhs_ty
                            .weaken_into(&ctx)
                            .with_cons(|rhs_term| {
                                let expected = rhs_inhab.app(&rhs_term);
                                let got = {
                                    rhs_term
                                    .inj_rhs(&lhs_name, &lhs_ty)
                                    .case(
                                        |elim| motive.app(&elim).to_ty(),
                                        |lhs_term| lhs_inhab.app(&lhs_term),
                                        |rhs_term| rhs_inhab.app(&rhs_term),
                                    )
                                };
                                assert_eq!(expected, got);
                            });
                        });
                    });
                });
            });
        });
    });
}

#[test]
fn proj_beta() {
    let ctx: Ctx<Infallible> = Ctx::root();
    
    ctx
    .name()
    .with_cons(|head_name| {
        let head_name = head_name.to_name();

        head_name
        .ctx()
        .universe()
        .with_cons(|head_ty| {
            let head_ty = head_ty.to_ty();
            let tail_ty_ty = head_ty.pi(&head_name, |head_term| head_term.ctx().universe());

            tail_ty_ty
            .with_cons(|tail_ty| {
                let ctx = tail_ty.ctx();
                head_ty
                .weaken_into(&ctx)
                .with_cons(|head_term| {
                    let bound_tail_ty = tail_ty.app(&head_term).to_ty();
                    bound_tail_ty
                    .with_cons(|tail_term| {
                        let ctx = tail_term.ctx();
                        let pair_term = head_term.pair(
                            &head_name,
                            |head_term| tail_ty.app(&head_term).to_ty(),
                            &tail_term,
                        );

                        let expected = head_term.weaken_into(&ctx);
                        let got = pair_term.proj_head();
                        assert_eq!(expected, got);

                        let expected = tail_term;
                        let got = pair_term.proj_tail();
                        assert_eq!(expected, got);
                    });
                });
            });
        });
    });
}

#[test]
fn pair_eta() {
    let ctx: Ctx<Infallible> = Ctx::root();

    ctx
    .name()
    .with_cons(|head_name| {
        let head_name = head_name.to_name();

        head_name
        .ctx()
        .universe()
        .with_cons(|head_ty| {
            let head_ty = head_ty.to_ty();
            
            let sigma_ty = head_ty.sigma(&head_name, |head_term| head_term.ctx().unit_ty());
            sigma_ty
            .with_cons(|pair_term| {
                let ctx = pair_term.ctx();
                assert_eq!(pair_term.proj_tail(), ctx.unit_term());

                let got = {
                    pair_term
                    .proj_head()
                    .pair(
                        &head_name,
                        |head_term| head_term.ctx().unit_ty(),
                        &pair_term.proj_tail(),
                    )
                };
                assert_eq!(pair_term, got);
            });

            let tail_ty_ty = head_ty.pi(&head_name, |head_term| head_term.ctx().universe());
            tail_ty_ty
            .with_cons(|tail_ty| {
                let ctx = tail_ty.ctx();
                let sigma_ty = {
                    head_ty
                    .weaken_into(&ctx)
                    .sigma(&head_name, |head_term| tail_ty.app(&head_term).to_ty())
                };
                sigma_ty
                .with_cons(|pair_term| {
                    let got = {
                        pair_term
                        .proj_head()
                        .pair(
                            &head_name,
                            |head_term| tail_ty.app(&head_term).to_ty(),
                            &pair_term.proj_tail(),
                        )
                    };
                    assert_eq!(pair_term, got);
                });
            });
        });

        let tail_ty_ty = {
            ctx
            .unit_ty()
            .pi(&head_name, |head_term| head_term.ctx().universe())
        };

        tail_ty_ty
        .with_cons(|tail_ty| {
            let ctx = tail_ty.ctx();
            let sigma_ty = {
                ctx
                .unit_ty().sigma(&head_name, |head_term| tail_ty.app(&head_term).to_ty())
            };
            sigma_ty
            .with_cons(|pair_term| {
                let ctx = pair_term.ctx();
                assert_eq!(pair_term.proj_head(), ctx.unit_term());

                let got = {
                    pair_term
                    .proj_head()
                    .pair(
                        &head_name,
                        |head_term| tail_ty.app(&head_term).to_ty(),
                        &pair_term.proj_tail(),
                    )
                };
                assert_eq!(pair_term, got);
            });
        });

        let sigma_ty = {
            ctx
            .unit_ty()
            .sigma(&head_name, |head_term| head_term.ctx().unit_ty())
        };
        sigma_ty
        .with_cons(|pair_term| {
            let ctx = pair_term.ctx();
            let expected = {
                ctx
                .unit_term()
                .pair(&head_name, |head_term| head_term.ctx().unit_ty(), &ctx.unit_term())
            };
            assert_eq!(expected, pair_term);
        });
    });
}

#[test]
fn func_eta() {
    let ctx: Ctx<Infallible> = Ctx::root();

    ctx
    .with_names(|[arg_name]| {
        arg_name
        .ctx()
        .universe()
        .with_cons(|arg_ty| {
            let arg_ty = arg_ty.to_ty();
            let res_ty_ty = arg_ty.pi(&arg_name, |arg_term| arg_term.ctx().universe());

            res_ty_ty
            .with_cons(|res_ty| {
                let ctx = res_ty.ctx();
                let pi_ty = arg_ty.weaken_into(&ctx).pi(&arg_name, |arg_term| res_ty.app(&arg_term).to_ty());

                pi_ty
                .with_cons(|func_term| {
                    let ctx = func_term.ctx();
                    let got = {
                        arg_ty
                        .weaken_into(&ctx)
                        .func(&arg_name, |arg_term| func_term.app(&arg_term))
                    };
                    assert_eq!(func_term, got);
                });
            });
        });

        let res_ty_ty = ctx.unit_ty().pi(&arg_name, |arg_term| arg_term.ctx().universe());
        
        res_ty_ty
        .with_cons(|res_ty| {
            let ctx = res_ty.ctx();
            let pi_ty = ctx.unit_ty().pi(&arg_name, |arg_term| res_ty.app(&arg_term).to_ty());

            pi_ty
            .with_cons(|func_term| {
                let ctx = func_term.ctx();
                let got = {
                    ctx
                    .unit_ty()
                    .func(&arg_name, |arg_term| func_term.app(&arg_term.ctx().unit_term()))
                };
                assert_eq!(func_term, got);
            });
        });
    });
}

