use crate::priv_prelude::*;

fn check_simplifies_at_depth(
    input_ty: &Ty,
    expected_output_ty: &Ty,
    depth: u32,
) {
    let (input_ty, expected_output_ty) = Ctx::into_common_ctx((input_ty, expected_output_ty));
    let constraint_name = TagScheme::name_from_str("constraint");

    let (_, iso) = Iso::simplify_ty(&input_ty, &constraint_name, depth);
    assert_eq!(
        iso.output_ty(),
        expected_output_ty,
    );

    let (_, iso) = Iso::simplify_ty(&input_ty, &constraint_name, (depth + 1) * 2);
    assert_eq!(
        iso.output_ty(),
        expected_output_ty,
    );

    if let Some(depth) = depth.checked_sub(1) {
        let (_, iso) = Iso::simplify_ty(&input_ty, &constraint_name, depth);
        assert_ne!(
            iso.output_ty(),
            expected_output_ty,
        );
    }
}

#[test]
fn simplify_universe() {
    let ctx = Ctx::root();

    check_simplifies_at_depth(
        &ctx.universe(),
        &ctx.universe(),
        0,
    );
}

#[test]
fn simplify_equal_arbitrary_terms() {
    let ctx = Ctx::root();

    ctx
    .universe()
    .with_cons(|eq_ty| {
        let eq_ty = eq_ty.to_ty();

        eq_ty
        .with_cons(|eq_term_0| {
            eq_ty
            .weaken_into(&eq_term_0.ctx())
            .with_cons(|eq_term_1| {
                check_simplifies_at_depth(
                    &eq_term_0.equals(&eq_term_1),
                    &eq_term_0.equals(&eq_term_1),
                    0,
                );
            })
        })
    })
}

#[test]
fn simplify_never() {
    let ctx = Ctx::root();

    check_simplifies_at_depth(
        &ctx.never(),
        &ctx.never(),
        0,
    );
}

#[test]
fn simplify_unit() {
    let ctx = Ctx::root();

    check_simplifies_at_depth(
        &ctx.unit_ty(),
        &ctx.unit_ty(),
        0,
    );
}

#[test]
fn simplify_sum_arbitrary_tys() {
    let ctx = Ctx::root();

    ctx
    .with_names(|[lhs_name]| {
        lhs_name
        .ctx()
        .with_tys(|[lhs_ty, rhs_ty]| {
            check_simplifies_at_depth(
                &lhs_ty.sum(&lhs_name, &rhs_ty),
                &lhs_ty.sum(&lhs_name, &rhs_ty),
                0,
            );
        })
    })
}

#[test]
fn simplify_sigma_arbitrary_tys() {
    let ctx = Ctx::root();

    ctx
    .with_names(|[head_name]| {
        head_name
        .ctx()
        .with_tys(|[head_ty]| {
            head_ty
            .pi(&head_name, |head| head.ctx().universe())
            .with_cons(|tail_ty| {
                let head_ty = head_ty.weaken_into(&tail_ty.ctx());
                let tail_ty = head_ty.scope(|head| tail_ty.app(&head).to_ty());

                check_simplifies_at_depth(
                    &tail_ty.to_sigma(&head_name),
                    &tail_ty.to_sigma(&head_name),
                    0,
                );
            })
        })
    })
}

#[test]
fn simplify_pi_arbitrary_tys() {
    let ctx = Ctx::root();

    ctx
    .function_extensionality_ty()
    .with_cons(|funext| {
        funext
        .ctx()
        .with_names(|[arg_name]| {
            arg_name
            .ctx()
            .with_tys(|[arg_ty]| {
                arg_ty
                .pi(&arg_name, |arg| arg.ctx().universe())
                .with_cons(|res_ty| {
                    let arg_ty = arg_ty.weaken_into(&res_ty.ctx());
                    let res_ty = arg_ty.scope(|arg| res_ty.app(&arg).to_ty());

                    check_simplifies_at_depth(
                        &res_ty.to_pi(&arg_name),
                        &res_ty.to_pi(&arg_name),
                        0,
                    );
                })
            })
        })
    })
}

#[test]
fn simplify_reflexive_equality_to_unit() {
    let ctx = Ctx::root();

    ctx
    .universe()
    .with_cons(|ty| {
        let ty = ty.to_ty();

        ty
        .with_cons(|term| {
            check_simplifies_at_depth(
                &term.equals(&term),
                &term.ctx().unit_ty(),
                1,
            );
        })
    })
}

#[test]
fn simplify_equality_between_uninhabited_and_inhabited_type_to_never() {
    let ctx = Ctx::root();

    ctx
    .universe()
    .with_cons(|ty| {
        let ty = ty.to_ty();

        ty
        .with_cons(|term| {
            check_simplifies_at_depth(
                &term.ctx().never().to_term().equals(&ty.to_term()),
                &term.ctx().never(),
                1,
            );
            check_simplifies_at_depth(
                &ty.to_term().equals(&term.ctx().never().to_term()),
                &term.ctx().never(),
                1,
            );
        })
    })
}

#[test]
fn simplify_nat_succ_injective() {
    let ctx = Ctx::root();

    ctx
    .nat()
    .with_cons(|n0| {
        n0
        .ctx()
        .nat()
        .with_cons(|n1| {
            check_simplifies_at_depth(
                &n0.succs(1u32).equals(&n1.succs(1u32)),
                &n0.equals(&n1),
                1,
            );

            check_simplifies_at_depth(
                &n0.succs(5u32).equals(&n1.succs(3u32)),
                &n0.succs(2u32).equals(&n1),
                1,
            );

            check_simplifies_at_depth(
                &n0.succs(3u32).equals(&n1.succs(5u32)),
                &n0.equals(&n1.succs(2u32)),
                1,
            );
        })
    })
}

#[test]
fn simplify_equality_equality() {
    let ctx = Ctx::root();

    ctx
    .universe()
    .with_cons(|eq_ty| {
        let eq_ty = eq_ty.to_ty();

        eq_ty
        .with_cons(|eq_term_0| {
            eq_ty
            .weaken_into(&eq_term_0.ctx())
            .with_cons(|eq_term_1| {
                eq_term_0
                .equals(&eq_term_1)
                .with_cons(|eq_0| {
                    eq_term_0
                    .weaken_into(&eq_0.ctx())
                    .equals(&eq_term_1)
                    .with_cons(|eq_1| {
                        check_simplifies_at_depth(
                            &eq_0.equals(&eq_1),
                            &eq_0.ctx().unit_ty(),
                            1,
                        );
                    })
                })
            })
        })
    })
}

#[test]
fn simplify_sum_lhs_injective() {
    let ctx = Ctx::root();

    ctx
    .with_names(|[lhs_name]| {
        lhs_name
        .ctx()
        .with_tys(|[lhs_ty, rhs_ty]| {
            lhs_ty
            .with_cons(|lhs_term_0| {
                lhs_ty
                .weaken_into(&lhs_term_0.ctx())
                .with_cons(|lhs_term_1| {
                    check_simplifies_at_depth(
                        &lhs_term_0
                        .inj_lhs(&lhs_name, &rhs_ty)
                        .equals(&lhs_term_1.inj_lhs(&lhs_name, &rhs_ty)),
                        &lhs_term_0.equals(&lhs_term_1),
                        1,
                    );
                })
            })
        })
    })
}

#[test]
fn simplify_sum_rhs_injective() {
    let ctx = Ctx::root();

    ctx
    .with_names(|[lhs_name]| {
        lhs_name
        .ctx()
        .with_tys(|[lhs_ty, rhs_ty]| {
            rhs_ty
            .with_cons(|rhs_term_0| {
                rhs_ty
                .weaken_into(&rhs_term_0.ctx())
                .with_cons(|rhs_term_1| {
                    check_simplifies_at_depth(
                        &rhs_term_0
                        .inj_rhs(&lhs_name, &lhs_ty)
                        .equals(&rhs_term_1.inj_rhs(&lhs_name, &lhs_ty)),
                        &rhs_term_0.equals(&rhs_term_1),
                        1,
                    );
                })
            })
        })
    })
}

#[test]
fn simplify_sum_lhs_equals_rhs_to_never() {
    let ctx = Ctx::root();

    ctx
    .with_names(|[lhs_name]| {
        lhs_name
        .ctx()
        .with_tys(|[lhs_ty, rhs_ty]| {
            lhs_ty
            .with_cons(|lhs_term| {
                rhs_ty
                .weaken_into(&lhs_term.ctx())
                .with_cons(|rhs_term| {
                    check_simplifies_at_depth(
                        &lhs_term
                        .inj_lhs(&lhs_name, &rhs_ty)
                        .equals(&rhs_term.inj_rhs(&lhs_name, &lhs_ty)),
                        &rhs_term.ctx().never(),
                        1,
                    );

                    check_simplifies_at_depth(
                        &rhs_term
                        .inj_rhs(&lhs_name, &lhs_ty)
                        .equals(&lhs_term.inj_lhs(&lhs_name, &rhs_ty)),
                        &rhs_term.ctx().never(),
                        1,
                    );
                })
            })
        })
    })
}

#[test]
fn simplify_equality_between_pairs() {
    let ctx = Ctx::root();

    ctx
    .with_names(|[head_name]| {
        head_name
        .ctx()
        .with_tys(|[head_ty]| {
            head_ty
            .pi(&head_name, |head| head.ctx().universe())
            .with_cons(|tail_ty| {
                let head_ty = head_ty.weaken_into(&tail_ty.ctx());
                let tail_ty = head_ty.scope(|head| tail_ty.app(&head).to_ty());

                head_ty
                .with_cons(|head_0| {
                    head_ty
                    .weaken_into(&head_0.ctx())
                    .with_cons(|head_1| {
                        tail_ty
                        .weaken_into(&head_1.ctx())
                        .bind(&head_0)
                        .with_cons(|tail_0| {
                            tail_ty
                            .weaken_into(&tail_0.ctx())
                            .bind(&head_1)
                            .with_cons(|tail_1| {
                                check_simplifies_at_depth(
                                    &head_0
                                    .pair(&head_name, tail_ty.unbind(), &tail_0)
                                    .equals(&head_1.pair(&head_name, tail_ty.unbind(), &tail_1)),
                                    &head_0
                                    .equals(&head_1)
                                    .weaken_into(&tail_1.ctx())
                                    .sigma(&head_name, |head_eq| {
                                        tail_ty
                                        .bind_eq(&head_eq)
                                        .heterogeneous_equal(&tail_0, &tail_1)
                                    }),
                                    1,
                                );
                            })
                        })
                    })
                })
            })
        })
    })
}

#[test]
fn simplify_sum_never_lhs() {
    let ctx = Ctx::root();

    ctx
    .with_names(|[lhs_name]| {
        lhs_name
        .ctx()
        .with_tys(|[rhs_ty]| {
            check_simplifies_at_depth(
                &rhs_ty.ctx().never().sum(&lhs_name, &rhs_ty),
                &rhs_ty,
                1,
            );
        })
    })
}

#[test]
fn simplify_sum_never_rhs() {
    let ctx = Ctx::root();

    ctx
    .with_names(|[lhs_name]| {
        lhs_name
        .ctx()
        .with_tys(|[lhs_ty]| {
            check_simplifies_at_depth(
                &lhs_ty.sum(&lhs_name, &lhs_ty.ctx().never()),
                &lhs_ty,
                1,
            );
        })
    })
}


#[test]
fn simplify_sigma_never_head() {
    let ctx = Ctx::root();

    ctx
    .with_names(|[head_name]| {
        head_name
        .ctx()
        .never()
        .pi(&head_name, |never| never.ctx().universe())
        .with_cons(|tail_ty| {
            let tail_ty = tail_ty.ctx().never().scope(|never| tail_ty.app(&never).to_ty());

            check_simplifies_at_depth(
                &tail_ty.to_sigma(&head_name),
                &tail_ty.ctx().never(),
                1,
            );
        })
    })
}

#[test]
fn simplify_sigma_unit_head() {
    let ctx = Ctx::root();

    ctx
    .with_names(|[head_name]| {
        head_name
        .ctx()
        .unit_ty()
        .pi(&head_name, |unit| unit.ctx().universe())
        .with_cons(|tail_ty| {
            let tail_ty = tail_ty.ctx().unit_ty().scope(|unit| tail_ty.app(&unit).to_ty());

            check_simplifies_at_depth(
                &tail_ty.to_sigma(&head_name),
                &tail_ty.bind(&tail_ty.ctx().unit_term()),
                1,
            );
        })
    })
}

#[test]
fn simplify_sigma_never_tail() {
    let ctx = Ctx::root();

    ctx
    .with_names(|[head_name]| {
        head_name
        .ctx()
        .with_tys(|[head_ty]| {
            check_simplifies_at_depth(
                &head_ty.sigma(&head_name, |head| head.ctx().never()),
                &head_ty.ctx().never(),
                1,
            );
        })
    })
}

#[test]
fn simplify_sigma_unit_tail() {
    let ctx = Ctx::root();

    ctx
    .with_names(|[head_name]| {
        head_name
        .ctx()
        .with_tys(|[head_ty]| {
            check_simplifies_at_depth(
                &head_ty.sigma(&head_name, |head| head.ctx().unit_ty()),
                &head_ty,
                1,
            );
        })
    })
}

#[test]
fn simplify_sigma_constrained() {
    let ctx = Ctx::root();

    ctx
    .with_names(|[head_name]| {
        head_name
        .ctx()
        .with_tys(|[ty]| {
            ty
            .with_cons(|the_term| {
                let ty = ty.weaken_into(&the_term.ctx());

                check_simplifies_at_depth(
                    &ty.sigma(&head_name, |term| term.equals(&the_term)),
                    &ty.ctx().unit_ty(),
                    1,
                );
            })
        })
    })
}

#[test]
fn simplify_pi_never_arg() {
    let ctx = Ctx::root();

    ctx
    .function_extensionality_ty()
    .with_cons(|funext| {
        funext
        .ctx()
        .with_names(|[arg_name]| {
            arg_name
            .ctx()
            .never()
            .pi(&arg_name, |never| never.ctx().universe())
            .with_cons(|res_ty| {
                let res_ty = res_ty.ctx().never().scope(|never| res_ty.app(&never).to_ty());

                check_simplifies_at_depth(
                    &res_ty.to_pi(&arg_name),
                    &res_ty.ctx().unit_ty(),
                    1,
                );
            })
        })
    })
}

#[test]
fn simplify_pi_unit_arg() {
    let ctx = Ctx::root();

    ctx
    .function_extensionality_ty()
    .with_cons(|funext| {
        funext
        .ctx()
        .with_names(|[arg_name]| {
            arg_name
            .ctx()
            .unit_ty()
            .pi(&arg_name, |unit| unit.ctx().universe())
            .with_cons(|res_ty| {
                let res_ty = res_ty.ctx().unit_ty().scope(|unit| res_ty.app(&unit).to_ty());

                check_simplifies_at_depth(
                    &res_ty.to_pi(&arg_name),
                    &res_ty.bind(&res_ty.ctx().unit_term()),
                    1,
                );
            })
        })
    })
}

#[test]
fn simplify_pi_res_never_arg_inhabited() {
    let ctx = Ctx::root();

    ctx
    .function_extensionality_ty()
    .with_cons(|funext| {
        funext
        .ctx()
        .with_names(|[arg_name]| {
            arg_name
            .ctx()
            .with_tys(|[arg_ty]| {
                arg_ty
                .with_cons(|term| {
                    check_simplifies_at_depth(
                        &arg_ty
                        .weaken_into(&term.ctx())
                        .pi(&arg_name, |term| term.ctx().never()),
                        &term.ctx().never(),
                        1,
                    );
                })
            })
        })
    })
}

// TODO
// There's a bug where `sum == injr(rhs)` is getting "simplified" to
// `{case sum { injl(lhs) => injl(lhs), injr(rhs) => injr(rhs) }} == injr(rhs)`
// figure out why that is then reenable this test.
#[ignore]
#[test]
fn simplify_pi_res_refutable_equality() {
    let ctx = Ctx::root();

    ctx
    .function_extensionality_ty()
    .with_cons(|funext| {
        funext
        .ctx()
        .with_names(|[arg_name, lhs_name]| {
            arg_name
            .ctx()
            .with_tys(|[lhs_ty, rhs_ty]| {
                lhs_ty
                .with_cons(|lhs_term| {
                    rhs_ty
                    .weaken_into(&lhs_term.ctx())
                    .with_cons(|rhs_term| {
                        let lhs_ty = lhs_ty.weaken_into(&rhs_term.ctx());
                        let rhs_ty = rhs_ty.weaken_into(&rhs_term.ctx());

                        check_simplifies_at_depth(
                            &lhs_ty
                            .sum(&lhs_name, &rhs_ty)
                            .pi(&arg_name, |sum| {
                                sum.equals(&rhs_term.inj_rhs(&lhs_name, &lhs_ty))
                            }),
                            &rhs_term.ctx().never(),
                            1,
                        );
                    })
                })
            })
        })
    })
}

#[test]
fn simplify_pi_res_unit() {
    let ctx = Ctx::root();

    ctx
    .function_extensionality_ty()
    .with_cons(|funext| {
        funext
        .ctx()
        .with_names(|[arg_name]| {
            arg_name
            .ctx()
            .with_tys(|[arg_ty]| {
                check_simplifies_at_depth(
                    &arg_ty.pi(&arg_name, |arg| arg.ctx().unit_ty()),
                    &arg_ty.ctx().unit_ty(),
                    1,
                );
            })
        })
    })
}

#[test]
fn simplify_equality_of_sum_types_to_equality_of_type_parameters() {
    let ctx = Ctx::root();

    let lhs_name_eq_name = TagScheme::name_from_str("lhs_name_eq");
    let lhs_ty_eq_name = TagScheme::name_from_str("lhs_ty_eq");

    ctx
    .with_names(|[lhs_name_0, lhs_name_1]| {
        lhs_name_0
        .ctx()
        .with_tys(|[lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1]| {
            let (
                lhs_name_0,
                lhs_name_1,
                lhs_ty_0,
                lhs_ty_1,
                rhs_ty_0,
                rhs_ty_1,
            ) = Ctx::into_common_ctx((
                &lhs_name_0, &lhs_name_1, &lhs_ty_0, &lhs_ty_1, &rhs_ty_0, &rhs_ty_1,
            ));

            check_simplifies_at_depth(
                &lhs_ty_0
                .sum(&lhs_name_0, &rhs_ty_0)
                .to_term()
                .equals(&lhs_ty_1.sum(&lhs_name_1, &rhs_ty_1).to_term()),
                &lhs_name_0
                .to_term()
                .equals(&lhs_name_1.to_term())
                .sigma(
                    &lhs_name_eq_name,
                    |_| {
                        lhs_ty_0
                        .to_term()
                        .equals(&lhs_ty_1.to_term())
                        .weaken_into(&rhs_ty_1.ctx())
                        .sigma(
                            &lhs_ty_eq_name,
                            |_| rhs_ty_0.to_term().equals(&rhs_ty_1.to_term()),
                        )
                    },
                ),
                1,
            );
        })
    })
}

#[test]
fn simplify_equality_of_sigma_types_to_equality_of_type_parameters() {
    let ctx = Ctx::root();

    let head_name_eq_name = TagScheme::name_from_str("head_names_eq");
    let head_ty_eq_name = TagScheme::name_from_str("head_tys_eq");

    ctx
    .function_extensionality_ty()
    .with_cons(|funext| {
        funext
        .ctx()
        .with_names(|[head_name_0, head_name_1]| {
            head_name_0
            .ctx()
            .with_tys(|[head_ty_0, head_ty_1]| {
                head_ty_0
                .pi(&head_name_0, |head| head.ctx().universe())
                .with_cons(|tail_ty_0| {
                    let (head_ty_0, head_ty_1, tail_ty_0) = Ctx::into_common_ctx((
                        &head_ty_0, &head_ty_1, &tail_ty_0,
                    ));
                    let tail_ty_0 = head_ty_0.scope(|head| tail_ty_0.app(&head).to_ty());

                    head_ty_1
                    .pi(&head_name_1, |head| head.ctx().universe())
                    .with_cons(|tail_ty_1| {
                        let (
                            head_name_0, head_name_1,
                            head_ty_0, head_ty_1,
                            tail_ty_0, tail_ty_1,
                        ) = Ctx::into_common_ctx((
                            &head_name_0, &head_name_1,
                            &head_ty_0, &head_ty_1,
                            &tail_ty_0, &tail_ty_1,
                        ));
                        let tail_ty_1 = head_ty_1.scope(|head| tail_ty_1.app(&head).to_ty());

                        check_simplifies_at_depth(
                            &tail_ty_0
                            .to_sigma(&head_name_0)
                            .to_term()
                            .equals(
                                &tail_ty_1
                                .to_sigma(&head_name_1)
                                .to_term()
                            ),
                            &head_name_0
                            .to_term()
                            .equals(&head_name_1.to_term())
                            .sigma(
                                &head_name_eq_name,
                                |head_name_eq| {
                                    let (head_ty_0, head_name_eq) = Ctx::into_common_ctx((
                                        &head_ty_0, &head_name_eq,
                                    ));

                                    head_ty_0
                                    .to_term()
                                    .equals(&head_ty_1.to_term())
                                    .sigma(
                                        &head_ty_eq_name,
                                        |head_ty_eq| {
                                            Ty::scoped_tys_equal(
                                                &head_name_eq,
                                                &head_ty_eq,
                                                tail_ty_0.unbind(),
                                                tail_ty_1.unbind(),
                                            )
                                        },
                                    )
                                },
                            ),
                            1,
                        );
                    })
                })
            })
        })
    })
}

#[test]
fn simplify_equality_of_pi_types_to_equality_of_type_parameters() {
    let ctx = Ctx::root();

    let arg_name_eq_name = TagScheme::name_from_str("arg_names_eq");
    let arg_ty_eq_name = TagScheme::name_from_str("arg_tys_eq");

    ctx
    .function_extensionality_ty()
    .with_cons(|funext| {
        funext
        .ctx()
        .with_names(|[arg_name_0, arg_name_1]| {
            arg_name_0
            .ctx()
            .with_tys(|[arg_ty_0, arg_ty_1]| {
                arg_ty_0
                .pi(&arg_name_0, |arg| arg.ctx().universe())
                .with_cons(|res_ty_0| {
                    let (arg_ty_0, arg_ty_1, res_ty_0) = Ctx::into_common_ctx((
                        &arg_ty_0, &arg_ty_1, &res_ty_0,
                    ));
                    let res_ty_0 = arg_ty_0.scope(|arg| res_ty_0.app(&arg).to_ty());

                    arg_ty_1
                    .pi(&arg_name_1, |arg| arg.ctx().universe())
                    .with_cons(|res_ty_1| {
                        let (
                            arg_name_0, arg_name_1,
                            arg_ty_0, arg_ty_1,
                            res_ty_0, res_ty_1,
                        ) = Ctx::into_common_ctx((
                            &arg_name_0, &arg_name_1,
                            &arg_ty_0, &arg_ty_1,
                            &res_ty_0, &res_ty_1,
                        ));
                        let res_ty_1 = arg_ty_1.scope(|arg| res_ty_1.app(&arg).to_ty());

                        check_simplifies_at_depth(
                            &res_ty_0
                            .to_pi(&arg_name_0)
                            .to_term()
                            .equals(
                                &res_ty_1
                                .to_pi(&arg_name_1)
                                .to_term()
                            ),
                            &arg_name_0
                            .to_term()
                            .equals(&arg_name_1.to_term())
                            .sigma(
                                &arg_name_eq_name,
                                |arg_name_eq| {
                                    let (arg_ty_0, arg_name_eq) = Ctx::into_common_ctx((
                                        &arg_ty_0, &arg_name_eq,
                                    ));

                                    arg_ty_0
                                    .to_term()
                                    .equals(&arg_ty_1.to_term())
                                    .sigma(
                                        &arg_ty_eq_name,
                                        |arg_ty_eq| {
                                            Ty::scoped_tys_equal(
                                                &arg_name_eq,
                                                &arg_ty_eq,
                                                res_ty_0.unbind(),
                                                res_ty_1.unbind(),
                                            )
                                        },
                                    )
                                },
                            ),
                            1,
                        );
                    })
                })
            })
        })
    })
}

#[test]
fn simplify_equality_of_lambdas_to_pointwise_equality_of_lambdas() {
    let ctx = Ctx::root();

    ctx
    .function_extensionality_ty()
    .with_cons(|funext| {
        funext
        .ctx()
        .with_names(|[arg_name]| {
            arg_name
            .ctx()
            .with_tys(|[arg_ty, res_ty]| {
                res_ty
                .with_cons(|res_term_0| {
                    res_ty
                    .weaken_into(&res_term_0.ctx())
                    .with_cons(|res_term_1| {
                        let arg_ty = arg_ty.weaken_into(&res_term_1.ctx());

                        check_simplifies_at_depth(
                            &arg_ty
                            .func(&arg_name, |_| res_term_0.clone())
                            .equals(
                                &arg_ty
                                .func(&arg_name, |_| res_term_1.clone())
                            ),
                            &arg_ty
                            .pi(&arg_name, |_| {
                                res_term_0.equals(&res_term_1)
                            }),
                            1,
                        )
                    })
                })
            })
        })
    })
}

/*
#[test]
fn simplify_equality_of_sigma_types_to_equality_of_type_parameters() {
    let ctx = Ctx::root();

    ctx
    .universe()
    .with_cons(|head_ty_0| {
        let head_ty_0 = head_ty_0.to_ty();

        head_ty_0
        .ctx()
        .universe()
        .with_cons(|head_ty_1| {
            let head_ty_1 = head_ty_1.to_ty();

            head_ty_0
            .weaken_into(&head_ty_1.ctx())
            .pi(|head_0| head_0.ctx().universe())
            .with_cons(|tail_ty_0| {
                let head_ty_0 = head_ty_0.weaken_into(&tail_ty_0.ctx());
                let tail_ty_0 = head_ty_0.scope(|head_0| tail_ty_0.app(&head_0).to_ty());

                head_ty_1
                .weaken_into(&tail_ty_0.ctx())
                .pi(|head_1| head_1.ctx().universe())
                .with_cons(|tail_ty_1| {
                    let head_ty_0 = head_ty_0.weaken_into(&tail_ty_1.ctx());
                    let head_ty_1 = head_ty_1.weaken_into(&tail_ty_1.ctx());
                    let tail_ty_0 = tail_ty_0.weaken_into(&tail_ty_1.ctx());
                    let tail_ty_1 = head_ty_1.scope(|head_1| tail_ty_1.app(&head_1).to_ty());

                    check_simplifies_at_depth(
                        &head_ty_0
                        .sigma(tail_ty_0.unbind())
                        .to_term()
                        .equals(&head_ty_1.sigma(tail_ty_1.unbind()).to_term()),
                        &head_ty_0
                        .to_term()
                        .equals(&head_ty_1.to_term())
                        .sigma(|head_eq| {
                            head_eq
                            .scoped_tys_equal(tail_ty_0.unbind(), tail_ty_1.unbind())
                        }),
                        1,
                    );
                })
            })
        })
    })
}

#[test]
fn simplify_equality_of_pi_types_to_equality_of_type_parameters() {
    let ctx = Ctx::root();

    ctx
    .universe()
    .with_cons(|arg_ty_0| {
        let arg_ty_0 = arg_ty_0.to_ty();

        arg_ty_0
        .ctx()
        .universe()
        .with_cons(|arg_ty_1| {
            let arg_ty_1 = arg_ty_1.to_ty();

            arg_ty_0
            .weaken_into(&arg_ty_1.ctx())
            .pi(|arg_0| arg_0.ctx().universe())
            .with_cons(|res_ty_0| {
                let arg_ty_0 = arg_ty_0.weaken_into(&res_ty_0.ctx());
                let res_ty_0 = arg_ty_0.scope(|arg_0| res_ty_0.app(&arg_0).to_ty());

                arg_ty_1
                .weaken_into(&res_ty_0.ctx())
                .pi(|arg_1| arg_1.ctx().universe())
                .with_cons(|res_ty_1| {
                    let arg_ty_0 = arg_ty_0.weaken_into(&res_ty_1.ctx());
                    let arg_ty_1 = arg_ty_1.weaken_into(&res_ty_1.ctx());
                    let res_ty_0 = res_ty_0.weaken_into(&res_ty_1.ctx());
                    let res_ty_1 = arg_ty_1.scope(|arg_1| res_ty_1.app(&arg_1).to_ty());

                    check_simplifies_at_depth(
                        &arg_ty_0
                        .pi(res_ty_0.unbind())
                        .to_term()
                        .equals(&arg_ty_1.pi(res_ty_1.unbind()).to_term()),
                        &arg_ty_0
                        .to_term()
                        .equals(&arg_ty_1.to_term())
                        .sigma(|arg_eq| {
                            arg_eq
                            .scoped_tys_equal(res_ty_0.unbind(), res_ty_1.unbind())
                        }),
                        1,
                    );
                })
            })
        })
    })
}
*/

