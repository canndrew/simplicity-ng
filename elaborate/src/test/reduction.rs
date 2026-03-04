use crate::priv_prelude::*;

lazy_static! {
    static ref CONSTRAINT_NAME: Name = TagScheme::name_from_str("constraint");
}

#[allow(unused)]
fn check_reduction_steps(
    scope: InferScope<Tm>,
    target_ty: Ty,
    max_steps: u32,
) {
    for recursion_depth in 0..max_steps {
        let reduction = scope.reduce_constraint(recursion_depth);
        if reduction.new_constraint_ty() == target_ty {
            panic!("reduced in {} steps", recursion_depth);
        }
    }
    panic!("failed to reduce in {} steps", max_steps);
}

fn assert_generically_reduces_to(
    from_ty: &Ty,
    into_ty: &Ty,
    recursion_depth: u32,
) {
    from_ty
    .pi(&CONSTRAINT_NAME, |term| term.ctx().universe())
    .with_cons(|body_ty| {
        from_ty
        .weaken_into(&body_ty.ctx())
        .pi(&CONSTRAINT_NAME, |term| body_ty.app(&term).to_ty())
        .with_cons(|body| {
            let scope = {
                from_ty
                .weaken_into(&body.ctx())
                .scope(|term| {
                    body.app(&term)
                })
            };
            let scope = InferScope::from_scope(&CONSTRAINT_NAME, &scope);

            if let Some(recursion_depth) = recursion_depth.checked_sub(1) {
                let reduction = scope.reduce_constraint(recursion_depth);
                assert_ne!(reduction.new_constraint_ty(), into_ty.weaken_into(&body.ctx()));
            }

            let reduction = scope.reduce_constraint(recursion_depth);
            assert_eq!(reduction.new_constraint_ty(), into_ty.weaken_into(&body.ctx()));

            let reduction = scope.reduce_constraint((recursion_depth + 1) * 2);
            assert_eq!(reduction.new_constraint_ty(), into_ty.weaken_into(&body.ctx()));
        })
    });
}

#[test]
fn reduce_irrelevant() {
    let ctx = Ctx::root();
    let scope = ctx.universe().scope(|term| {
        term.ctx().unit_term()
    });
    let reduction = InferScope::from_scope(&CONSTRAINT_NAME, &scope).reduce_constraint(1);
    assert_eq!(reduction.new_constraint_ty(), ctx.unit_ty());
}

#[test]
fn reduce_never() {
    let never = Ctx::root().never();
    assert_generically_reduces_to(&never, &never, 0);
}

#[test]
fn reduce_unit() {
    let unit_ty = Ctx::root().unit_ty();
    assert_generically_reduces_to(&unit_ty, &unit_ty, 0);
}

#[test]
fn reduce_arbitrary_type_irreducible() {
    Ctx::root().universe().with_cons(|ty| {
        let ty = ty.to_ty();
        assert_generically_reduces_to(&ty, &ty, 0);
    });
}

#[test]
fn reduce_arbitrary_sum_type_irreducible() {
    Ctx::root()
    .with_names(|[lhs_name]| {
        lhs_name
        .ctx()
        .with_tys(|[lhs_ty, rhs_ty]| {
            let sum_ty = lhs_ty.sum(&lhs_name, &rhs_ty);
            assert_generically_reduces_to(&sum_ty, &sum_ty, 0);
        })
    })
}

#[test]
fn reduce_sum_of_never() {
    Ctx::root()
    .with_names(|[lhs_name]| {
        lhs_name
        .ctx()
        .with_tys(|[ty]| {
            let never = ty.ctx().never();

            assert_generically_reduces_to(&ty.sum(&lhs_name, &never), &ty, 1);
            assert_generically_reduces_to(&never.sum(&lhs_name, &ty), &ty, 1);
            assert_generically_reduces_to(&never.sum(&lhs_name, &never), &never, 1);
        })
    })
}

#[test]
fn reduce_arbitrary_sigma_type_irreducible() {
    Ctx::root()
    .with_names(|[head_name]| {
        head_name
        .ctx()
        .with_tys(|[head_ty]| {
            head_ty
            .pi(&head_name, |head| head.ctx().universe())
            .with_cons(|tail_ty| {
                let sigma_ty = {
                    head_ty
                    .weaken_into(&tail_ty.ctx())
                    .sigma(&head_name, |head| tail_ty.app(&head).to_ty())
                };
                assert_generically_reduces_to(&sigma_ty, &sigma_ty, 0);
            })
        })
    })
}

#[test]
fn reduce_sigma_never_tail() {
    Ctx::root()
    .with_names(|[head_name]| {
        head_name
        .ctx()
        .with_tys(|[head_ty]| {
            let sigma_ty = {
                head_ty
                .sigma(&head_name, |head| head.ctx().never())
            };
            assert_generically_reduces_to(
                &sigma_ty,
                &head_ty.ctx().never(),
                1,
            );
        })
    })
}

#[test]
fn reduce_sigma_never_head() {
    Ctx::root()
    .with_names(|[head_name]| {
        head_name
        .ctx()
        .never()
        .pi(&head_name, |never| never.ctx().universe())
        .with_cons(|tail_ty| {
            assert_generically_reduces_to(
                &tail_ty.ctx().never().sigma(&head_name, |never| tail_ty.app(&never).to_ty()),
                &tail_ty.ctx().never(),
                1,
            );
        })
    })
}

#[test]
fn reduce_sigma_unit_tail() {
    Ctx::root()
    .with_names(|[head_name]| {
        head_name
        .ctx()
        .with_tys(|[head_ty]| {
            assert_generically_reduces_to(
                &head_ty.sigma(&head_name, |head| head.ctx().unit_ty()),
                &head_ty,
                1,
            );
        })
    })
}

#[test]
fn reduce_sigma_unit_head() {
    Ctx::root()
    .with_names(|[head_name]| {
        head_name
        .ctx()
        .unit_ty()
        .pi(&head_name, |unit| unit.ctx().universe())
        .with_cons(|tail_ty| {
            assert_generically_reduces_to(
                &tail_ty.ctx().unit_ty().sigma(&head_name, |unit| tail_ty.app(&unit).to_ty()),
                &tail_ty.app(&tail_ty.ctx().unit_term()).to_ty(),
                1,
            );
        })
    })
}

#[test]
fn reduce_arbitrary_pi_type_irreducible() {
    Ctx::root()
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
                    let pi_ty = res_ty.to_pi(&arg_name);
                    assert_generically_reduces_to(
                        &pi_ty,
                        &pi_ty,
                        0,
                    );
                });
            })
        })
    })
}

#[test]
fn reduce_reflexive_equality() {
    Ctx::root()
    .with_tys(|[eq_ty]| {
        eq_ty
        .with_cons(|eq_term| {
            assert_generically_reduces_to(
                &eq_term.equals(&eq_term),
                &eq_term.ctx().unit_ty(),
                1,
            );
        })
    })
}

#[test]
fn reduce_equality_of_different_tags_to_never() {
    let ctx = Ctx::root();
    let name_0 = TagScheme::name_from_str("tag_0");
    let name_1 = TagScheme::name_from_str("tag_1");

    assert_generically_reduces_to(
        &name_0.to_term().equals(&name_1.to_term()),
        &ctx.never(),
        1,
    );
}

#[test]
fn reduce_uninhabited_inhabited_equality_to_never() {
    let ctx = Ctx::root();
    assert_generically_reduces_to(
        &ctx.never().to_term().equals(&ctx.unit_ty().to_term()),
        &ctx.never(),
        1,
    );
    assert_generically_reduces_to(
        &ctx.unit_ty().to_term().equals(&ctx.never().to_term()),
        &ctx.never(),
        1,
    );
}

#[test]
fn reduce_inj_lhs_equals_inj_lhs_to_equality_of_lhs_terms() {
    Ctx::root()
    .with_names(|[lhs_name]| {
        lhs_name
        .ctx()
        .with_tys(|[lhs_ty, rhs_ty]| {
            lhs_ty
            .with_cons(|lhs_term_0| {
                lhs_ty
                .weaken_into(&lhs_term_0.ctx())
                .with_cons(|lhs_term_1| {
                    assert_generically_reduces_to(
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
fn reduce_inj_rhs_equals_inj_rhs_to_equality_of_rhs_terms() {
    Ctx::root()
    .with_names(|[lhs_name]| {
        lhs_name
        .ctx()
        .with_tys(|[lhs_ty, rhs_ty]| {
            rhs_ty
            .with_cons(|rhs_term_0| {
                rhs_ty
                .weaken_into(&rhs_term_0.ctx())
                .with_cons(|rhs_term_1| {
                    assert_generically_reduces_to(
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
fn reduce_inj_lhs_rhs_equality_mismatch_to_never() {
    Ctx::root()
    .with_names(|[lhs_name]| {
        lhs_name
        .ctx()
        .with_tys(|[lhs_ty, rhs_ty]| {
            lhs_ty
            .with_cons(|lhs_term| {
                rhs_ty
                .weaken_into(&lhs_term.ctx())
                .with_cons(|rhs_term| {
                    assert_generically_reduces_to(
                        &lhs_term
                        .inj_lhs(&lhs_name, &rhs_ty)
                        .equals(&rhs_term.inj_rhs(&lhs_name, &lhs_ty)),
                        &rhs_term.ctx().never(),
                        1,
                    );
                    assert_generically_reduces_to(
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
fn reduce_equality_of_pairs_to_pair_of_equalities() {
    Ctx::root()
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
                                assert_generically_reduces_to(
                                    &head_0
                                    .pair(&head_name, tail_ty.unbind(), &tail_0)
                                    .equals(
                                        &head_1
                                        .pair(&head_name, tail_ty.unbind(), &tail_1)
                                    ),
                                    &head_0
                                    .equals(&head_1)
                                    .weaken_into(&tail_1.ctx())
                                    .sigma(&head_name, |head_eq| {
                                        tail_ty
                                        .bind_eq(&head_eq)
                                        .heterogeneous_equal(&tail_0, &tail_1)
                                    }),
                                    1,
                                )
                            })
                        })
                    })
                })
            })
        })
    })
}

#[test]
fn reduce_equality_of_equality_tys() {
    Ctx::root()
    .with_tys(|[eq_ty_0, eq_ty_1]| {
        eq_ty_0
        .with_cons(|eq_term_0_0| {
            eq_ty_0
            .weaken_into(&eq_term_0_0.ctx())
            .with_cons(|eq_term_1_0| {
                eq_ty_1
                .weaken_into(&eq_term_1_0.ctx())
                .with_cons(|eq_term_0_1| {
                    eq_ty_1
                    .weaken_into(&eq_term_0_1.ctx())
                    .with_cons(|eq_term_1_1| {
                        let ty_eq_name = TagScheme::name_from_str("ty_eq");
                        let val_0_eq_name = TagScheme::name_from_str("val_0_eq");
                        let val_1_eq_name = TagScheme::name_from_str("val_1_eq");

                        let val_0_0_name = TagScheme::name_from_str("val_0_0");
                        let val_1_0_name = TagScheme::name_from_str("val_0_0");
                        let val_0_1_name = TagScheme::name_from_str("val_0_1");
                        let val_1_1_name = TagScheme::name_from_str("val_0_1");

                        assert_generically_reduces_to(
                            &eq_term_0_0
                            .equals(&eq_term_1_0)
                            .to_term()
                            .equals(
                                &eq_term_0_1
                                .equals(&eq_term_1_1)
                                .to_term()
                            ),
                            &eq_ty_0
                            .to_term()
                            .equals(&eq_ty_1.to_term())
                            .weaken_into(&eq_term_1_1.ctx())
                            .sigma(&ty_eq_name, |eq_ty_equal| {
                                eq_ty_equal
                                .cong(
                                    |eq_ty_0, eq_ty_1, _eq_ty_equal| {
                                        let eq_ty_0 = eq_ty_0.to_ty();
                                        let eq_ty_1 = eq_ty_1.to_ty();

                                        eq_ty_0
                                        .pi(&val_0_0_name, |eq_term_0_0| {
                                            eq_ty_0
                                            .weaken_into(&eq_term_0_0.ctx())
                                            .pi(&val_1_0_name, |eq_term_1_0| {
                                                eq_ty_1
                                                .weaken_into(&eq_term_1_0.ctx())
                                                .pi(&val_0_1_name, |eq_term_0_1| {
                                                    eq_ty_1
                                                    .weaken_into(&eq_term_0_1.ctx())
                                                    .pi(&val_1_1_name, |eq_term_1_1| {
                                                        eq_term_1_1.ctx().universe()
                                                    })
                                                })
                                            })
                                        })
                                    },
                                    |eq_ty| {
                                        let eq_ty = eq_ty.to_ty();

                                        eq_ty
                                        .func(&val_0_0_name, |eq_term_0_0| {
                                            eq_ty
                                            .weaken_into(&eq_term_0_0.ctx())
                                            .func(&val_1_0_name, |eq_term_1_0| {
                                                eq_ty
                                                .weaken_into(&eq_term_1_0.ctx())
                                                .func(&val_0_1_name, |eq_term_0_1| {
                                                    eq_ty
                                                    .weaken_into(&eq_term_0_1.ctx())
                                                    .func(&val_1_1_name, |eq_term_1_1| {
                                                        eq_term_0_0
                                                        .equals(&eq_term_0_1)
                                                        .weaken_into(&eq_term_1_1.ctx())
                                                        .sigma(&val_0_eq_name, |eq_term_0_equal| {
                                                            eq_term_1_0
                                                            .equals(&eq_term_1_1)
                                                            .weaken_into(&eq_term_0_equal.ctx())
                                                            .sigma(&val_1_eq_name, |eq_term_1_equal| {
                                                                eq_term_1_equal.ctx().unit_ty()
                                                            })
                                                        })
                                                        .to_term()
                                                    })
                                                })
                                            })
                                        })
                                    },
                                )
                                .app(&eq_term_0_0)
                                .app(&eq_term_1_0)
                                .app(&eq_term_0_1)
                                .app(&eq_term_1_1)
                                .to_ty()
                            }),
                            1
                        )
                    })
                })
            })
        })
    })
}

#[test]
fn reduce_equality_of_sum_tys() {
    let lhs_name_eq_name = TagScheme::name_from_str("lhs_name_eq");
    let lhs_ty_eq_name = TagScheme::name_from_str("lhs_ty_eq");

    Ctx::root()
    .with_names(|[lhs_name_0, lhs_name_1]| {
        lhs_name_0
        .ctx()
        .with_tys(|[lhs_ty_0, rhs_ty_0, lhs_ty_1, rhs_ty_1]| {
            let lhs_name_0 = lhs_name_0.weaken_into(&lhs_ty_0.ctx());
            let lhs_name_1 = lhs_name_1.weaken_into(&lhs_ty_0.ctx());

            assert_generically_reduces_to(
                &lhs_ty_0
                .sum(&lhs_name_0, &rhs_ty_0)
                .to_term()
                .equals(
                    &lhs_ty_1
                    .sum(&lhs_name_1, &rhs_ty_1)
                    .to_term()
                ),
                &lhs_name_0
                .to_term()
                .equals(&lhs_name_1.to_term())
                .sigma(&lhs_name_eq_name, |_| {
                    lhs_ty_0
                    .to_term()
                    .equals(&lhs_ty_1.to_term())
                    .sigma(&lhs_ty_eq_name, |_| {
                        rhs_ty_0
                        .to_term()
                        .equals(&rhs_ty_1.to_term())
                    })
                }),
                1,
            );
        })
    })
}

#[test]
fn reduce_equality_of_sigma_tys() {
    let head_name_eq_name = TagScheme::name_from_str("head_name_eq");
    let head_ty_eq_name = TagScheme::name_from_str("head_ty_eq");

    let tail_ty_0_name = TagScheme::name_from_str("tail_ty_0");
    let tail_ty_1_name = TagScheme::name_from_str("tail_ty_1");

    Ctx::root()
    .with_names(|[head_name_0, head_name_1]| {
        head_name_0
        .ctx()
        .with_tys(|[head_ty_0, head_ty_1]| {
            let head_name_0 = head_name_0.weaken_into(&head_ty_0.ctx());
            let head_name_1 = head_name_1.weaken_into(&head_ty_0.ctx());

            head_ty_0
            .pi(&head_name_0, |head| head.ctx().universe())
            .with_cons(|tail_ty_0| {
                let head_ty_0 = head_ty_0.weaken_into(&tail_ty_0.ctx());
                let tail_ty_0 = head_ty_0.scope(|head| tail_ty_0.app(&head).to_ty());

                head_ty_1
                .weaken_into(&tail_ty_0.ctx())
                .pi(&head_name_1, |head| head.ctx().universe())
                .with_cons(|tail_ty_1| {
                    let head_name_0 = head_name_0.weaken_into(&tail_ty_1.ctx());
                    let head_name_1 = head_name_1.weaken_into(&tail_ty_1.ctx());
                    let head_ty_0 = head_ty_0.weaken_into(&tail_ty_1.ctx());
                    let head_ty_1 = head_ty_1.weaken_into(&tail_ty_1.ctx());
                    let tail_ty_0 = tail_ty_0.weaken_into(&tail_ty_1.ctx());
                    let tail_ty_1 = head_ty_1.scope(|head| tail_ty_1.app(&head).to_ty());

                    assert_generically_reduces_to(
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
                        .sigma(&head_name_eq_name, |head_name_eq| {
                            head_ty_0
                            .to_term()
                            .equals(&head_ty_1.to_term())
                            .weaken_into(&head_name_eq.ctx())
                            .sigma(&head_ty_eq_name, |head_ty_eq| {
                                head_name_eq
                                .weaken_into(&head_ty_eq.ctx())
                                .cong(
                                    |head_name_0, head_name_1, head_name_eq| {
                                        let head_name_0 = head_name_0.to_name();
                                        let head_name_1 = head_name_1.to_name();

                                        head_ty_0
                                        .weaken_into(&head_name_eq.ctx())
                                        .pi(&head_name_0, |head| head.ctx().universe())
                                        .pi(&tail_ty_0_name, |tail_ty_0| {
                                            head_ty_1
                                            .weaken_into(&tail_ty_0.ctx())
                                            .pi(&head_name_1, |head| head.ctx().universe())
                                            .pi(&tail_ty_1_name, |tail_ty_1| {
                                                tail_ty_1.ctx().universe()
                                            })
                                        })
                                    },
                                    |head_name| {
                                        let head_name = head_name.to_name();

                                        head_ty_eq
                                        .weaken_into(&head_name.ctx())
                                        .cong(
                                            |head_ty_0, head_ty_1, _| {
                                                let head_ty_0 = head_ty_0.to_ty();
                                                let head_ty_1 = head_ty_1.to_ty();

                                                head_ty_0
                                                .pi(&head_name, |head| {
                                                    head.ctx().universe()
                                                })
                                                .pi(&tail_ty_0_name, |tail_ty_0| {
                                                    head_ty_1
                                                    .weaken_into(&tail_ty_0.ctx())
                                                    .pi(&head_name, |head| {
                                                        head.ctx().universe()
                                                    })
                                                    .pi(&tail_ty_1_name, |tail_ty_1| {
                                                        tail_ty_1.ctx().universe()
                                                    })
                                                })
                                            },
                                            |head_ty| {
                                                let head_ty = head_ty.to_ty();

                                                head_ty
                                                .pi(&head_name, |head| head.ctx().universe())
                                                .func(&tail_ty_0_name, |tail_ty_0| {
                                                    head_ty
                                                    .weaken_into(&tail_ty_0.ctx())
                                                    .pi(&head_name, |head| {
                                                        head.ctx().universe()
                                                    })
                                                    .func(&tail_ty_1_name, |tail_ty_1| {
                                                        tail_ty_0.equals(&tail_ty_1).to_term()
                                                    })
                                                })
                                            },
                                        )
                                    },
                                )
                                .app(&head_ty_0.func(&head_name_0, |head| tail_ty_0.bind(&head).to_term()))
                                .app(&head_ty_1.func(&head_name_1, |head| tail_ty_1.bind(&head).to_term()))
                                .to_ty()
                            })
                        }),
                        1,
                    )
                })
            })
        })
    })
}

