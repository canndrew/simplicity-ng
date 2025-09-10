use crate::priv_prelude::*;

#[test]
fn reduce_irrelevant() {
    let ctx = Ctx::<!>::root();
    let infer_scope = ctx.ty_hole().map(|_, term| {
        term.ctx().unit_term()
    });
    let reduction = infer_scope.scope.reduce_constraint(1);
    assert_eq!(reduction.new_var_ty(), ctx.unit_ty());
}

fn assert_generically_reduces_to(
    from_ty: &Ty<!>,
    into_ty: &Ty<!>,
    recursion_depth: u32,
) {
    from_ty.pi(|term| term.ctx().universe()).with_cons(|inner_ty| {
        from_ty
        .weaken_into(&inner_ty.ctx())
        .pi(|term| inner_ty.app(&term).to_ty())
        .with_cons(|inner_term| {
            let infer_scope = {
                from_ty
                .weaken_into(&inner_term.ctx())
                .hole()
                .map(|_, term| {
                    inner_term.app(&term)
                })
            };
            let reduction = infer_scope.scope.reduce_constraint(recursion_depth);
            assert_eq!(reduction.new_var_ty(), into_ty.weaken_into(&inner_term.ctx()));
        })
    });
}

#[test]
fn reduce_never() {
    let never = Ctx::root().never();
    assert_generically_reduces_to(&never, &never, 1);
}

#[test]
fn reduce_unit() {
    let unit_ty = Ctx::root().unit_ty();
    assert_generically_reduces_to(&unit_ty, &unit_ty, 1);
}

#[test]
fn reduce_arbitrary_type_irreducible() {
    let ctx = Ctx::<!>::root();
    ctx.universe().with_cons(|ty| {
        let ty = ty.to_ty();
        assert_generically_reduces_to(&ty, &ty, 10);
    });
}

#[test]
fn reduce_arbitrary_sum_type_irreducible() {
    let ctx = Ctx::<!>::root();
    ctx.universe().with_cons(|lhs_ty| {
        let lhs_ty = lhs_ty.to_ty();
        lhs_ty.ctx().universe().with_cons(|rhs_ty| {
            let rhs_ty = rhs_ty.to_ty();
            let sum_ty = Ty::sum(&lhs_ty, &rhs_ty);
            assert_generically_reduces_to(&sum_ty, &sum_ty, 10);
        });
    });
}

#[test]
fn reduce_arbitrary_sigma_type_irreducible() {
    let ctx = Ctx::<!>::root();
    ctx.universe().with_cons(|head_ty| {
        let head_ty = head_ty.to_ty();
        head_ty
        .pi(|head| head.ctx().universe())
        .with_cons(|tail_ty| {
            let sigma_ty = {
                head_ty
                .weaken_into(&tail_ty.ctx())
                .sigma(|head| tail_ty.app(&head).to_ty())
            };
            assert_generically_reduces_to(&sigma_ty, &sigma_ty, 10);
        });
    });
}

#[test]
fn reduce_arbitrary_pi_type_irreducible() {
    let ctx = Ctx::<!>::root();
    ctx.universe().with_cons(|arg_ty| {
        let arg_ty = arg_ty.to_ty();
        arg_ty
        .pi(|arg| arg.ctx().universe())
        .with_cons(|res_ty| {
            let pi_ty = {
                arg_ty
                .weaken_into(&res_ty.ctx())
                .sigma(|arg| res_ty.app(&arg).to_ty())
            };
            assert_generically_reduces_to(&pi_ty, &pi_ty, 10);
        });
    });
}

#[test]
fn reduce_sum_of_never() {
    let ctx = Ctx::<!>::root();
    ctx.universe().with_cons(|ty| {
        let ty = ty.to_ty();
        let never = ty.ctx().never();

        assert_generically_reduces_to(&Ty::sum(&ty, &never), &ty, 1);
        assert_generically_reduces_to(&Ty::sum(&never, &ty), &ty, 1);
        assert_generically_reduces_to(&Ty::sum(&never, &never), &never, 1);
    });
}

#[test]
fn reduce_sigma_never_tail() {
    let ctx = Ctx::<!>::root();
    ctx.universe().with_cons(|head_ty| {
        let head_ty = head_ty.to_ty();
        let never = head_ty.ctx().never();
        assert_generically_reduces_to(&head_ty.sigma(|_| never.clone()), &never, 1);
    });
}

#[test]
fn reduce_sigma_never_head() {
    let ctx = Ctx::<!>::root();
    ctx
    .never()
    .pi(|never| never.ctx().universe())
    .with_cons(|tail_ty| {
        assert_generically_reduces_to(
            &tail_ty.ctx().never().sigma(|never| tail_ty.app(&never).to_ty()),
            &tail_ty.ctx().never(),
            1,
        );
    })
}

#[test]
fn reduce_sigma_unit_tail() {
    let ctx = Ctx::<!>::root();
    ctx.universe().with_cons(|head_ty| {
        let head_ty = head_ty.to_ty();
        let unit_ty = head_ty.ctx().unit_ty();
        assert_generically_reduces_to(&head_ty.sigma(|_| unit_ty), &head_ty, 1);
    });
}

#[test]
fn reduce_sigma_unit_head() {
    let ctx = Ctx::<!>::root();
    ctx
    .unit_ty()
    .pi(|unit| unit.ctx().universe())
    .with_cons(|tail_ty| {
        assert_generically_reduces_to(
            &tail_ty.ctx().unit_ty().sigma(|unit| tail_ty.app(&unit).to_ty()),
            &tail_ty.app(&tail_ty.ctx().unit_term()).to_ty(),
            1,
        );
    })
}

#[test]
fn reduce_reflexive_equality() {
    let ctx = Ctx::<!>::root();
    ctx.universe().with_cons(|eq_ty| {
        eq_ty.to_ty().with_cons(|eq_term| {
            assert_generically_reduces_to(
                &eq_term.equals(&eq_term),
                &eq_term.ctx().unit_ty(),
                1,
            );
        })
    })
}

#[test]
fn reduce_uninhabited_inhabited_equality_to_never() {
    let ctx = Ctx::<!>::root();
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
fn reduce_equality_of_unequal_nats_to_never() {
    let ctx = Ctx::<!>::root();
    ctx.nat().with_cons(|n| {
        assert_generically_reduces_to(
            &n.ctx().zero().equals(&n.succs(1u32)),
            &n.ctx().never(),
            1,
        );
        assert_generically_reduces_to(
            &n.succs(1u32).equals(&n.ctx().zero()),
            &n.ctx().never(),
            1,
        );
    });
}

#[test]
fn reduce_succ_equals_succ_to_equality_of_predecessors() {
    let ctx = Ctx::<!>::root();
    ctx.nat().with_cons(|n0| {
        n0.ctx().nat().with_cons(|n1| {
            assert_generically_reduces_to(
                &n0.succs(1u32).equals(&n1.succs(1u32)),
                &n0.equals(&n1),
                1,
            );
            assert_generically_reduces_to(
                &n0.succs(2u32).equals(&n1.succs(2u32)),
                &n0.equals(&n1),
                1,
            );
            assert_generically_reduces_to(
                &n0.succs(1u32).equals(&n1.succs(2u32)),
                &n0.equals(&n1.succs(1u32)),
                1,
            );
        });
    });
}

#[test]
fn reduce_inj_lhs_equals_inj_lhs_to_equality_of_lhs_terms() {
    let ctx = Ctx::<!>::root();
    ctx.universe().with_cons(|lhs_ty| {
        let lhs_ty = lhs_ty.to_ty();
        lhs_ty.ctx().universe().with_cons(|rhs_ty| {
            let rhs_ty = rhs_ty.to_ty();
            lhs_ty.weaken_into(&rhs_ty.ctx()).with_cons(|lhs_term_0| {
                lhs_ty.weaken_into(&lhs_term_0.ctx()).with_cons(|lhs_term_1| {
                    assert_generically_reduces_to(
                        &lhs_term_0.inj_lhs(&rhs_ty).equals(&lhs_term_1.inj_lhs(&rhs_ty)),
                        &lhs_term_0.equals(&lhs_term_1),
                        1,
                    );
                })
            });
        });
    })
}

#[test]
fn reduce_inj_rhs_equals_inj_rhs_to_equality_of_rhs_terms() {
    let ctx = Ctx::<!>::root();
    ctx.universe().with_cons(|lhs_ty| {
        let lhs_ty = lhs_ty.to_ty();
        lhs_ty.ctx().universe().with_cons(|rhs_ty| {
            let rhs_ty = rhs_ty.to_ty();
            rhs_ty.with_cons(|rhs_term_0| {
                rhs_ty.weaken_into(&rhs_term_0.ctx()).with_cons(|rhs_term_1| {
                    assert_generically_reduces_to(
                        &rhs_term_0.inj_rhs(&lhs_ty).equals(&rhs_term_1.inj_rhs(&lhs_ty)),
                        &rhs_term_0.equals(&rhs_term_1),
                        1,
                    );
                })
            });
        });
    })
}

/*
 *  forall
 *      Lhs : Type
 *      Rhs : Type
 *      lhs : Lhs
 *      rhs : Rhs
 *
 *  the constraint types:
 *
 *      {.lhs lhs} == {.rhs rhs}
 *      and
 *      {.rhs rhs} == {.lhs lhs}
 *
 *  both reduce to:
 *
 *      enum {}
 */
#[test]
fn reduce_inj_lhs_rhs_equality_mismatch_to_never() {
    let ctx = Ctx::<!>::root();
    ctx.universe().with_cons(|lhs_ty| {
        let lhs_ty = lhs_ty.to_ty();
        lhs_ty.ctx().universe().with_cons(|rhs_ty| {
            let rhs_ty = rhs_ty.to_ty();
            lhs_ty.weaken_into(&rhs_ty.ctx()).with_cons(|lhs_term| {
                rhs_ty.weaken_into(&lhs_term.ctx()).with_cons(|rhs_term| {
                    let never = rhs_term.ctx().never();
                    assert_generically_reduces_to(
                        &lhs_term.inj_lhs(&rhs_ty).equals(&rhs_term.inj_rhs(&lhs_ty)),
                        &never,
                        1,
                    );
                    assert_generically_reduces_to(
                        &rhs_term.inj_rhs(&lhs_ty).equals(&lhs_term.inj_lhs(&rhs_ty)),
                        &never,
                        1,
                    );
                })
            });
        });
    })
}


/*
 *  forall
 *      Head : Type
 *      Tail : Type
 *      head_0 : Head
 *      head_1 : Head
 *      tail_0 : Tail
 *      tail_1 : Tail
 *
 *  the constraint type:
 *
 *      (head = head_0, tail = tail_0) == (head = head_1, tail = tail_1)
 *
 *  reduces to:
 *
 *      struct {
 *          head_eq: head_0 == head_1,
 *          tail_eq: tail_0 == tail_1,
 *      }
 */
#[test]
fn reduce_equality_of_non_dependent_pairs_to_pair_of_equalities() {
    let ctx = Ctx::<!>::root();
    ctx.universe().with_cons(|head_ty| {
        let head_ty = head_ty.to_ty();

        head_ty
        .ctx()
        .universe()
        .with_cons(|tail_ty| {
            let tail_ty = tail_ty.to_ty();

            head_ty
            .weaken_into(&tail_ty.ctx())
            .with_cons(|head_0| {
                head_ty
                .weaken_into(&head_0.ctx())
                .with_cons(|head_1| {
                    tail_ty
                    .weaken_into(&head_1.ctx())
                    .with_cons(|tail_0| {
                        tail_ty
                        .weaken_into(&tail_0.ctx())
                        .with_cons(|tail_1| {
                            assert_generically_reduces_to(
                                &head_0
                                .pair(|_| tail_ty.clone(), &tail_0)
                                .equals(
                                    &head_1.pair(|_| tail_ty.clone(), &tail_1),
                                ),
                                &head_0
                                .equals(&head_1)
                                .weaken_into(&tail_1.ctx())
                                .sigma(|_|tail_0.equals(&tail_1)),
                                1,
                            );
                        })
                    })
                })
            })
        })
    })
}


/*
 *  forall
 *      Head : Type
 *      Tail : Fn(head: Head) -> Type
 *      head_0 : Head
 *      head_1 : Head
 *      tail_0 : Tail(head = head_0)
 *      tail_1 : Tail(head = head_1)
 *
 *  the constraint type:
 *
 *      (head = head_0, tail = tail_0) == (head = head_1, tail = tail_1)
 *
 *  reduces to:
 *
 *      struct {
 *          head_eq: head_0 == head_1,
 *          tail_eq: cong(
 *              elim = head_eq,
 *              Motive(head_0, head_1, head_eq) = Fn(
 *                  tail_0: Tail(head = head_0),
 *                  tail_1: Tail(head = head_1),
 *              ) -> Type,
 *              inhab(head, tail_0, tail_1) = tail_0 == tail_1,
 *              tail_0,
 *              tail_1,
 *          ),
 *      }
 *
 */
#[test]
fn reduce_equality_of_pairs_to_pair_of_equalities() {
    let ctx = Ctx::<!>::root();
    ctx.universe().with_cons(|head_ty| {
        let head_ty = head_ty.to_ty();

        head_ty
        .pi(|head| head.ctx().universe())
        .with_cons(|tail_ty| {
            let tail_ty = tail_ty.to_scope().map(|_, tail_ty| tail_ty.to_ty());

            head_ty
            .weaken_into(&tail_ty.ctx())
            .with_cons(|head_0| {
                head_ty
                .weaken_into(&head_0.ctx())
                .with_cons(|head_1| {
                    tail_ty
                    .bind(&head_0)
                    .weaken_into(&head_1.ctx())
                    .with_cons(|tail_0| {
                        tail_ty
                        .bind(&head_1)
                        .weaken_into(&tail_0.ctx())
                        .with_cons(|tail_1| {
                            assert_generically_reduces_to(
                                &head_0
                                .pair(tail_ty.unbind(), &tail_0)
                                .equals(
                                    &head_1.pair(tail_ty.unbind(), &tail_1),
                                ),
                                &head_0
                                .equals(&head_1)
                                .weaken_into(&tail_1.ctx())
                                .sigma(|head_eq| {
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
}


/*
 *  forall
 *      Head : Type
 *      head : Head
 *
 *  the constraint type:
 *
 *      struct {
 *          this_head: Head,
 *          head_eq: this_head == head,
 *      }
 *
 *  reduces to:
 *
 *      struct {}
 */
#[test]
fn reduce_sigma_constrained() {
    let ctx = Ctx::<!>::root();
    ctx.universe().with_cons(|head_ty| {
        let head_ty = head_ty.to_ty();

        head_ty.with_cons(|head| {
            let head_ty = head_ty.weaken_into(&head.ctx());
            assert_generically_reduces_to(
                &head_ty.sigma(|this_head| this_head.equals(&head)),
                &head.ctx().unit_ty(),
                2,
            );
        });
    });
}

/*
 *  forall
 *      Lhs0 : Type
 *      Lhs1 : Type
 *      Rhs0 : Type
 *      Rhs1 : Type
 *
 *  the constraint type:
 *
 *      {enum { lhs: Lhs0, rhs: Rhs0 }} == {enum { lhs: Lhs1, rhs: Rhs1 }}
 *
 *  reduces to:
 *
 *      struct {
 *          lhs_ty_eq: Lhs0 == Lhs1,
 *          rhs_ty_eq: Rhs0 == Rhs1,
 *      }
 */
#[test]
fn reduce_sum_type_equality() {
    let ctx = Ctx::<!>::root();
    ctx.universe().with_cons(|lhs_ty_0| {
        lhs_ty_0.ctx().universe().with_cons(|lhs_ty_1| {
            lhs_ty_1.ctx().universe().with_cons(|rhs_ty_0| {
                rhs_ty_0.ctx().universe().with_cons(|rhs_ty_1| {
                    let lhs_ty_0 = lhs_ty_0.to_ty();
                    let lhs_ty_1 = lhs_ty_1.to_ty();
                    let rhs_ty_0 = rhs_ty_0.to_ty();
                    let rhs_ty_1 = rhs_ty_1.to_ty();

                    let sum_ty_0 = Ty::sum(&lhs_ty_0, &rhs_ty_0);
                    let sum_ty_1 = Ty::sum(&lhs_ty_1, &rhs_ty_1);
                    let sum_ty_eq_ty = sum_ty_0.to_term().equals(&sum_ty_1.to_term());

                    let lhs_ty_eq_ty = lhs_ty_0.to_term().equals(&lhs_ty_1.to_term());
                    let rhs_ty_eq_ty = rhs_ty_0.to_term().equals(&rhs_ty_1.to_term());
                    let sigma_ty = {
                        lhs_ty_eq_ty
                        .weaken_into(&rhs_ty_1.ctx())
                        .sigma(|_| rhs_ty_eq_ty)
                    };

                    assert_generically_reduces_to(
                        &sum_ty_eq_ty,
                        &sigma_ty,
                        1,
                    );
                });
            });
        });
    });
}

/*
 *  forall
 *      Head0: Type
 *      Head1: Type,
 *      Tail0: Fn(head: Head0) -> Type
 *      Tail1: Fn(head: Head1) -> Type
 *
 *  the constraint type:
 *  
 *      {struct { head: Head0, tail: Tail0(head) }} == {struct { head: Head1, tail: Tail1(head) }}
 *
 *  reduces to:
 *
 *      struct {
 *          head_ty_eq: Head0 == Head1,
 *          tail_ty_eq: cong(
 *              elim = head_ty_eq,
 *              Motive(Head0, Head1, head_ty_eq) = Fn(
 *                  Tail0: (head: Head0) -> Type,
 *                  Tail1: (head: Head1) -> Type,
 *              ) -> Type,
 *              inhab(Head, Tail0, Tail1) = Tail0 == Tail1,
 *              Tail0,
 *              Tail1,
 *          ),
 *      }
 */
#[test]
fn reduce_sigma_type_equality() {
    let ctx = Ctx::<!>::root();
    ctx.universe().with_cons(|head_ty_0| {
        let head_ty_0 = head_ty_0.to_ty();

        head_ty_0.ctx().universe().with_cons(|head_ty_1| {
            let head_ty_1 = head_ty_1.to_ty();

            head_ty_0
            .weaken_into(&head_ty_1.ctx())
            .pi(|head| head.ctx().universe())
            .with_cons(|tail_ty_0| {
                let tail_ty_0 = head_ty_0.weaken_into(&tail_ty_0.ctx()).scope(|head| {
                    tail_ty_0.app(&head).to_ty()
                });

                head_ty_1
                .weaken_into(&tail_ty_0.ctx())
                .pi(|head| head.ctx().universe())
                .with_cons(|tail_ty_1| {
                    let tail_ty_1 = head_ty_1.weaken_into(&tail_ty_1.ctx()).scope(|head| {
                        tail_ty_1.app(&head).to_ty()
                    });

                    let head_ty_0 = head_ty_0.weaken_into(&tail_ty_1.ctx());
                    let head_ty_1 = head_ty_1.weaken_into(&tail_ty_1.ctx());
                    let tail_ty_0 = tail_ty_0.weaken_into(&tail_ty_1.ctx());

                    let sigma_ty_0 = head_ty_0.sigma(tail_ty_0.unbind());
                    let sigma_ty_1 = head_ty_1.sigma(tail_ty_1.unbind());
                    let sigma_ty_eq_ty = sigma_ty_0.to_term().equals(&sigma_ty_1.to_term());

                    let head_ty_eq_ty = head_ty_0.to_term().equals(&head_ty_1.to_term());
                    let tail_ty_eq_ty = head_ty_eq_ty.scope(|head_ty_eq| {
                        head_ty_eq
                        .scoped_tys_equal(tail_ty_0.unbind(), tail_ty_1.unbind())
                    });
                    let eq_sigma_ty = head_ty_eq_ty.sigma(tail_ty_eq_ty.unbind());

                    assert_generically_reduces_to(
                        &sigma_ty_eq_ty,
                        &eq_sigma_ty,
                        1,
                    );
                });
            });
        });
    });
}


/*
 *  forall
 *      Arg0: Type
 *      Arg1: Type,
 *      Res0: Fn(arg: Arg0) -> Type
 *      Res0: Fn(arg: Arg1) -> Type
 *
 *  the constraint type:
 *  
 *      {Fn(arg: Arg0) -> Res0(arg)} == {Fn(arg: Arg1) -> Res1(arg)}
 *
 *  reduces to:
 *
 *      struct {
 *          arg_ty_eq: Arg0 == Arg1,
 *          res_ty_eq: cong(
 *              elim = arg_ty_eq,
 *              Motive(Arg0, Arg1, arg_ty_eq) = Fn(
 *                  Res0: (arg: Arg0) -> Type,
 *                  Res1: (arg: Arg1) -> Type,
 *              ) -> Type,
 *              inhab(Arg, Res0, Res1) = Res0 == Res1,
 *              Res0,
 *              Res1,
 *          ),
 *      }
 */
#[test]
fn reduce_pi_type_equality() {
    let ctx = Ctx::<!>::root();
    ctx.universe().with_cons(|arg_ty_0| {
        let arg_ty_0 = arg_ty_0.to_ty();

        arg_ty_0.ctx().universe().with_cons(|arg_ty_1| {
            let arg_ty_1 = arg_ty_1.to_ty();

            arg_ty_0
            .weaken_into(&arg_ty_1.ctx())
            .pi(|arg| arg.ctx().universe())
            .with_cons(|res_ty_0| {
                let res_ty_0 = arg_ty_0.weaken_into(&res_ty_0.ctx()).scope(|arg| {
                    res_ty_0.app(&arg).to_ty()
                });

                arg_ty_1
                .weaken_into(&res_ty_0.ctx())
                .pi(|arg| arg.ctx().universe())
                .with_cons(|res_ty_1| {
                    let res_ty_1 = arg_ty_1.weaken_into(&res_ty_1.ctx()).scope(|arg| {
                        res_ty_1.app(&arg).to_ty()
                    });

                    let arg_ty_0 = arg_ty_0.weaken_into(&res_ty_1.ctx());
                    let arg_ty_1 = arg_ty_1.weaken_into(&res_ty_1.ctx());
                    let res_ty_0 = res_ty_0.weaken_into(&res_ty_1.ctx());

                    let pi_ty_0 = arg_ty_0.pi(res_ty_0.unbind());
                    let pi_ty_1 = arg_ty_1.pi(res_ty_1.unbind());
                    let pi_ty_eq_ty = pi_ty_0.to_term().equals(&pi_ty_1.to_term());

                    let arg_ty_eq_ty = arg_ty_0.to_term().equals(&arg_ty_1.to_term());
                    let res_ty_eq_ty = arg_ty_eq_ty.scope(|arg_ty_eq| {
                        arg_ty_eq
                        .scoped_tys_equal(res_ty_0.unbind(), res_ty_1.unbind())
                    });
                    let eq_sigma_ty = arg_ty_eq_ty.sigma(res_ty_eq_ty.unbind());

                    assert_generically_reduces_to(
                        &pi_ty_eq_ty,
                        &eq_sigma_ty,
                        1,
                    );
                });
            });
        });
    });
}


/*
 *  forall
 *      EqTy0 : Type
 *      EqTy1 : Type
 *      eq_term_0_0 : EqTy0
 *      eq_term_1_0 : EqTy0
 *      eq_term_0_1 : EqTy1
 *      eq_term_1_1 : EqTy1
 *
 *  the constraint type:
 *
 *      {eq_term_0_0 == eq_term_1_0} == {eq_term_0_1 == eq_term_1_1}
 *
 *  reduces to:
 *
 *      struct {
 *          eq_ty_eq: EqTy0 == EqTy1,
 *          eq_term_0_eq: cong(
 *              elim = eq_ty_eq,
 *              Motive(EqTy0, EqTy1, eq_ty_eq) = Fn(
 *                  eq_term_0_0: EqTy0,
 *                  eq_term_0_1: EqTy1,
 *              ) -> Type,
 *              inhab(EqTy, eq_term_0_0, eq_term_0_1) = {eq_term_0_0 == eq_term_0_1},
 *              eq_term_0_0,
 *              eq_term_0_1,
 *          ),
 *          eq_term_1_eq: cong(
 *              elim = eq_ty_eq,
 *              Motive(EqTy0, EqTy1, eq_ty_eq) = Fn(
 *                  eq_term_1_0: EqTy0,
 *                  eq_term_1_1: EqTy1,
 *              ) -> Type,
 *              inhab(EqTy, eq_term_1_0, eq_term_1_1) = {eq_term_1_0 == eq_term_1_1},
 *              eq_term_1_0,
 *              eq_term_1_1,
 *          ),
 *      }
 *      
 */
#[test]
fn reduce_equal_type_equality() {
    let ctx = Ctx::<!>::root();
    ctx.universe().with_cons(|eq_ty_0| {
        let eq_ty_0 = eq_ty_0.to_ty();

        eq_ty_0.ctx().universe().with_cons(|eq_ty_1| {
            let eq_ty_1 = eq_ty_1.to_ty();

            eq_ty_0.weaken_into(&eq_ty_1.ctx()).with_cons(|eq_term_0_0| {
                eq_ty_0.weaken_into(&eq_term_0_0.ctx()).with_cons(|eq_term_1_0| {
                    eq_ty_1.weaken_into(&eq_term_1_0.ctx()).with_cons(|eq_term_0_1| {
                        eq_ty_1.weaken_into(&eq_term_0_1.ctx()).with_cons(|eq_term_1_1| {
                            let eq_ty_0 = eq_ty_0.weaken_into(&eq_term_1_1.ctx());
                            let eq_ty_1 = eq_ty_1.weaken_into(&eq_term_1_1.ctx());
                            let eq_term_0_0 = eq_term_0_0.weaken_into(&eq_term_1_1.ctx());
                            let eq_term_0_1 = eq_term_0_1.weaken_into(&eq_term_1_1.ctx());
                            let eq_term_1_0 = eq_term_1_0.weaken_into(&eq_term_1_1.ctx());

                            assert_generically_reduces_to(
                                &eq_term_0_0
                                .equals(&eq_term_1_0)
                                .to_term()
                                .equals(
                                    &eq_term_0_1
                                    .equals(&eq_term_1_1)
                                    .to_term(),
                                ),
                                &eq_ty_0
                                .to_term()
                                .equals(&eq_ty_1.to_term())
                                .sigma(|eq_ty_eq| {
                                    eq_ty_eq
                                    .heterogeneous_equal(
                                        &eq_term_0_0,
                                        &eq_term_0_1,
                                    )
                                    .sigma(|_| {
                                        eq_ty_eq
                                        .heterogeneous_equal(
                                            &eq_term_1_0,
                                            &eq_term_1_1,
                                        )
                                    })
                                }),
                                1,
                            );
                        });
                    });
                });
            });
        });
    });
}


/*
 *  forall
 *      Head : Type
 *      Tail : Fn(head: Head) -> Type
 *      head_val : Head
 *
 *  the constraint type:
 *
 *      struct {
 *          pair: struct {
 *              head: Head,
 *              tail: Tail(head),
 *          },
 *          head_eq: pair.head == head_val,
 *      }
 *
 *  reduces to:
 *
 *      Tail(head = head_val),
 */
#[test]
fn reduce_sigma_field_projection_constrained() {
    let ctx = Ctx::<!>::root();
    ctx.universe().with_cons(|head_ty| {
        let head_ty = head_ty.to_ty();

        head_ty
        .pi(|head| head.ctx().universe())
        .with_cons(|tail_ty| {
            let head_ty = head_ty.weaken_into(&tail_ty.ctx());
            let tail_ty = head_ty.scope(|head| tail_ty.app(&head).to_ty());

            head_ty
            .with_cons(|head| {
                let head_ty = head_ty.weaken_into(&head.ctx());
                let tail_ty = tail_ty.weaken_into(&head.ctx());

                assert_generically_reduces_to(
                    &head_ty
                    .sigma(tail_ty.unbind())
                    .sigma(|pair| pair.proj_head().equals(&head)),
                    &tail_ty.bind(&head),
                    4,
                );
            });
        });
    });
}


/*
 *  forall
 *      Lhs : Type
 *      Rhs : Type
 *      Tail : Fn(lhs: Lhs) -> Type
 *
 *  the constraint type:
 *
 *      struct {
 *          head: enum {
 *              lhs: Lhs,
 *              rhs: Rhs,
 *          },
 *          tail: match head {
 *              .lhs lhs => Tail(lhs),
 *              .rhs _ => enum {},
 *          },
 *      }
 *
 *  reduces to:
 *
 *      struct {
 *          lhs: Lhs,
 *          tail: Tail(lhs),
 *      }
 */
#[test]
fn reduce_sigma_sum_head_distribute() {
    let ctx = Ctx::<!>::root();
    ctx.universe().with_cons(|lhs_ty| {
        let lhs_ty = lhs_ty.to_ty();

        lhs_ty.ctx().universe().with_cons(|rhs_ty| {
            let rhs_ty = rhs_ty.to_ty();

            lhs_ty
            .weaken_into(&rhs_ty.ctx())
            .pi(|lhs| lhs.ctx().universe())
            .with_cons(|lhs_tail_ty| {
                let lhs_ty = lhs_ty.weaken_into(&lhs_tail_ty.ctx());
                let rhs_ty = rhs_ty.weaken_into(&lhs_tail_ty.ctx());
                let lhs_tail_ty = lhs_ty.scope(|lhs| lhs_tail_ty.app(&lhs).to_ty());

                assert_generically_reduces_to(
                    &Ty::sum(&lhs_ty, &rhs_ty)
                    .sigma(|sum| {
                        sum
                        .case(
                            |sum| sum.ctx().universe(),
                            |lhs| lhs_tail_ty.bind(&lhs).to_term(),
                            |rhs| rhs.ctx().never().to_term()
                        )
                        .to_ty()
                    }),
                    &lhs_ty.sigma(lhs_tail_ty.unbind()),
                    3,
                );
            });
        });
    });
}

