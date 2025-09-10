use crate::priv_prelude::*;

#[extension(pub trait TmExt)]
impl<S: Scheme> Tm<S> {
    fn symmetry(&self) -> Tm<S> {
        self
        .cong(
            |x0, x1, _| x1.equals(&x0),
            |x| x.refl(),
        )
    }

    fn transitivity(&self, other: &Tm<S>) -> Tm<S> {
        let (eq_0, eq_1) = Ctx::into_common_ctx(self, other);

        let TyKind::Equal { eq_term_1, .. } = eq_1.ty().kind() else {
            panic!();
        };
        eq_0
        .cong(
            |x0, x1, _| x1.equals(&eq_term_1).pi(|_| x0.equals(&eq_term_1)),
            |x| x.equals(&eq_term_1).func(|eq| eq),
        )
        .app(&other)
    }

    fn transport(&self, term: &Tm<S>) -> Tm<S> {
        self
        .cong(
            |ty_0, ty_1, _| ty_0.to_ty().pi(|_| ty_1.to_ty()),
            |ty| ty.to_ty().func(|arg| arg),
        )
        .app(&term)
    }

    fn heterogeneous_equal(&self, term_0: &Tm<S>, term_1: &Tm<S>) -> Ty<S> {
        self
        .cong(
            |ty_0, ty_1, _| {
                ty_0
                .to_ty()
                .pi(|val_0| {
                    ty_1
                    .weaken_into(&val_0.ctx())
                    .to_ty()
                    .pi(|val_1| val_1.ctx().universe())
                })
            },
            |ty| {
                ty
                .to_ty()
                .func(|val_0| {
                    ty
                    .weaken_into(&val_0.ctx())
                    .to_ty()
                    .func(|val_1| val_0.equals(&val_1).to_term())
                })
            },
        )
        .app(&term_0)
        .app(&term_1)
        .to_ty()
    }

    fn heterogeneous_transitivity(
        term_0: &Tm<S>,
        term_1: &Tm<S>,
        term_2: &Tm<S>,
        tys_eq_0: &Tm<S>,
        tys_eq_1: &Tm<S>,
        terms_eq_0: &Tm<S>,
        terms_eq_1: &Tm<S>,
    ) -> Tm<S> {
        let TyKind::Equal { eq_term_0: _, eq_term_1: ty_2 } = tys_eq_1.ty().kind() else {
            panic!("heterogeneous_transitivity(): tys_eq_1 is not an equality");
        };

        tys_eq_0
        .cong(
            |ty_0, ty_1, tys_eq_0| {
                ty_1
                .equals(&ty_2)
                .pi(|tys_eq_1| {
                    ty_0
                    .to_ty()
                    .weaken_into(&tys_eq_1.ctx())
                    .pi(|term_0| {
                        ty_1
                        .to_ty()
                        .weaken_into(&term_0.ctx())
                        .pi(|term_1| {
                            tys_eq_0
                            .heterogeneous_equal(&term_0, &term_1)
                            .pi(|terms_eq_0| {
                                tys_eq_1
                                .weaken_into(&terms_eq_0.ctx())
                                .heterogeneous_equal(&term_1, &term_2)
                                .pi(|_terms_eq_1| {
                                    tys_eq_0
                                    .transitivity(&tys_eq_1)
                                    .heterogeneous_equal(&term_0, &term_2)
                                })
                            })
                        })
                    })
                })
            },
            |ty| {
                ty
                .equals(&ty_2)
                .func(|tys_eq_1| {
                    tys_eq_1
                    .cong(
                        |ty, ty_2, tys_eq_1| {
                            ty_2
                            .to_ty()
                            .pi(|term_2| {
                                ty
                                .to_ty()
                                .weaken_into(&term_2.ctx())
                                .pi(|term_0| {
                                    ty
                                    .to_ty()
                                    .weaken_into(&term_0.ctx())
                                    .pi(|term_1| {
                                        term_0
                                        .equals(&term_1)
                                        .pi(|terms_eq_0| {
                                            tys_eq_1
                                            .heterogeneous_equal(&term_1, &term_2)
                                            .weaken_into(&terms_eq_0.ctx())
                                            .pi(|_terms_eq_1| {
                                                tys_eq_1
                                                .heterogeneous_equal(&term_0, &term_2)
                                            })
                                        })
                                    })
                                })
                            })
                        },
                        |ty| {
                            ty
                            .to_ty()
                            .func(|term_2| {
                                ty
                                .to_ty()
                                .weaken_into(&term_2.ctx())
                                .func(|term_0| {
                                    ty
                                    .to_ty()
                                    .weaken_into(&term_0.ctx())
                                    .func(|term_1| {
                                        term_0
                                        .equals(&term_1)
                                        .func(|terms_eq_0| {
                                            term_1
                                            .equals(&term_2)
                                            .weaken_into(&terms_eq_0.ctx())
                                            .func(|terms_eq_1| {
                                                terms_eq_0
                                                .transitivity(&terms_eq_1)
                                            })
                                        })
                                    })
                                })
                            })
                        },
                    )
                    .app(&term_2)
                })
            },
        )
        .app(&tys_eq_1)
        .app(&term_0)
        .app(&term_1)
        .app(&terms_eq_0)
        .app(&terms_eq_1)
    }

    fn scoped_tys_equal(
        &self,
        body_ty_0: impl FnOnce(Tm<S>) -> Ty<S>,
        body_ty_1: impl FnOnce(Tm<S>) -> Ty<S>,
    ) -> Ty<S> {
        let TyKind::Equal {
            eq_term_0: var_ty_0,
            eq_term_1: var_ty_1,
        } = self.ty().kind() else {
            panic!("not an equality");
        };

        let var_ty_0 = var_ty_0.to_ty();
        let var_ty_1 = var_ty_1.to_ty();

        let body_ty_0 = var_ty_0.scope(body_ty_0);
        let body_ty_1 = var_ty_1.scope(body_ty_1);

        self
        .cong(
            |var_ty_0, var_ty_1, _| {
                let var_ty_0 = var_ty_0.to_ty();
                let var_ty_1 = var_ty_1.to_ty();

                var_ty_0
                .pi(|var_0| var_0.ctx().universe())
                .pi(|body_ty_0| {
                    var_ty_1
                    .weaken_into(&body_ty_0.ctx())
                    .pi(|var_1| var_1.ctx().universe())
                    .pi(|body_ty_1| {
                        body_ty_1.ctx().universe()
                    })
                })
            },
            |var_ty| {
                let var_ty = var_ty.to_ty();

                var_ty
                .pi(|var| var.ctx().universe())
                .func(|body_ty_0| {
                    var_ty
                    .weaken_into(&body_ty_0.ctx())
                    .pi(|var| var.ctx().universe())
                    .func(|body_ty_1| {
                        body_ty_0.equals(&body_ty_1).to_term()
                    })
                })
            },
        )
        .app(&var_ty_0.func(|var_0| body_ty_0.bind(&var_0).to_term()))
        .app(&var_ty_1.func(|var_1| body_ty_1.bind(&var_1).to_term()))
        .to_ty()
    }

    fn scoped_tys_cong(
        &self,
        body_ty_0: impl FnOnce(Tm<S>) -> Ty<S>,
        body_ty_1: impl FnOnce(Tm<S>) -> Ty<S>,
        body_tys_eq: &Tm<S>,
        motive: impl FnOnce(Ty<S>, Ty<S>, Tm<S>, Tm<S>, Tm<S>, Tm<S>) -> Ty<S>,
        inhab: impl FnOnce(Ty<S>, Tm<S>) -> Tm<S>,
    ) -> Tm<S> {
        let TyKind::Equal {
            eq_term_0: var_ty_0,
            eq_term_1: var_ty_1,
        } = self.ty().kind() else {
            panic!("not an equality");
        };

        let var_ty_0 = var_ty_0.to_ty();
        let var_ty_1 = var_ty_1.to_ty();

        let body_ty_0 = var_ty_0.scope(body_ty_0);
        let body_ty_1 = var_ty_1.scope(body_ty_1);

        debug_assert_eq!(
            self.scoped_tys_equal(
                |var_0| body_ty_0.bind(&var_0),
                |var_1| body_ty_1.bind(&var_1),
            ),
            body_tys_eq.ty(),
        );

        let motive = self.ctx().universe().scope(|var_ty_0| {
            let var_ty_0 = var_ty_0.to_ty();
            var_ty_0.ctx().universe().scope(|var_ty_1| {
                let var_ty_1 = var_ty_1.to_ty();

                var_ty_0
                .weaken_into(&var_ty_1.ctx())
                .to_term()
                .equals(&var_ty_1.to_term())
                .scope(|var_tys_eq| {
                    var_ty_0
                    .weaken_into(&var_tys_eq.ctx())
                    .pi(|var_0| var_0.ctx().universe())
                    .scope(|body_ty_0| {
                        var_ty_1
                        .weaken_into(&body_ty_0.ctx())
                        .pi(|var_1| var_1.ctx().universe())
                        .scope(|body_ty_1| {
                            var_tys_eq
                            .weaken_into(&body_ty_1.ctx())
                            .scoped_tys_equal(
                                |var_0| body_ty_0.app(&var_0).to_ty(),
                                |var_1| body_ty_1.app(&var_1).to_ty(),
                            )
                            .scope(|body_tys_eq| {
                                let var_ty_0 = var_ty_0.weaken_into(&body_tys_eq.ctx());
                                let var_ty_1 = var_ty_1.weaken_into(&body_tys_eq.ctx());
                                let var_tys_eq = var_tys_eq.weaken_into(&body_tys_eq.ctx());
                                let body_ty_0 = body_ty_0.weaken_into(&body_tys_eq.ctx());
                                let body_ty_1 = body_ty_1.weaken_into(&body_tys_eq.ctx());
                                motive(
                                    var_ty_0,
                                    var_ty_1,
                                    var_tys_eq,
                                    body_ty_0,
                                    body_ty_1,
                                    body_tys_eq,
                                )
                            })
                        })
                    })
                })
            })
        });
        let inhab = self.ctx().universe().scope(|var_ty| {
            let var_ty = var_ty.to_ty();
            var_ty
            .pi(|var| var.ctx().universe())
            .scope(|body_ty| {
                inhab(var_ty.weaken_into(&body_ty.ctx()), body_ty)
            })
        });

        self
        .cong(
            |var_ty_0, var_ty_1, var_tys_eq| {
                let var_ty_0 = var_ty_0.to_ty();
                let var_ty_1 = var_ty_1.to_ty();

                var_ty_0
                .pi(|var_0| var_0.ctx().universe())
                .pi(|body_ty_0| {
                    var_ty_1
                    .weaken_into(&body_ty_0.ctx())
                    .pi(|var_1| var_1.ctx().universe())
                    .pi(|body_ty_1| {
                        var_tys_eq
                        .weaken_into(&body_ty_1.ctx())
                        .scoped_tys_equal(
                            |var_0| body_ty_0.app(&var_0).to_ty(),
                            |var_1| body_ty_1.app(&var_1).to_ty(),
                        )
                        .pi(|body_tys_eq| {
                            motive
                            .weaken_into(&body_tys_eq.ctx())
                            .bind(&var_ty_0.to_term())
                            .bind(&var_ty_1.to_term())
                            .bind(&var_tys_eq)
                            .bind(&body_ty_0)
                            .bind(&body_ty_1)
                            .bind(&body_tys_eq)
                        })
                    })
                })
            },
            |var_ty| {
                let var_ty = var_ty.to_ty();

                var_ty
                .pi(|var| var.ctx().universe())
                .func(|body_ty_0| {
                    var_ty
                    .weaken_into(&body_ty_0.ctx())
                    .pi(|var| var.ctx().universe())
                    .func(|body_ty_1| {
                        body_ty_0
                        .equals(&body_ty_1)
                        .func(|body_tys_eq| {
                            body_tys_eq
                            .cong(
                                |body_ty_0, body_ty_1, body_tys_eq| {
                                    motive
                                    .bind(&var_ty.to_term())
                                    .bind(&var_ty.to_term())
                                    .bind(&var_ty.to_term().refl())
                                    .bind(&body_ty_0)
                                    .bind(&body_ty_1)
                                    .bind(&body_tys_eq)
                                },
                                |body_ty| {
                                    inhab
                                    .bind(&var_ty.to_term())
                                    .bind(&body_ty)
                                },
                            )
                        })
                    })
                })
            },
        )
        .app(
            &var_ty_0.func(|var| body_ty_0.bind(&var).to_term()),
        )
        .app(
            &var_ty_1.func(|var| body_ty_1.bind(&var).to_term()),
        )
        .app(body_tys_eq)
    }

    fn pi_eq_cong(
        &self,
        motive: impl FnOnce(Ty<S>, Ty<S>, Tm<S>, Tm<S>, Tm<S>) -> Ty<S>,
        inhab: impl FnOnce(Ty<S>, Tm<S>) -> Tm<S>,
    ) -> Tm<S> {
        let TyKind::Equal { eq_term_0: pi_ty_0, eq_term_1: pi_ty_1 } = self.ty().kind() else {
            panic!("pi_eq_cong(): not an equality");
        };
        let TyKind::Pi { res_ty: res_ty_0 } = pi_ty_0.to_ty().kind() else {
            panic!("pi_eq_cong(): left side of equality is not a pi type");
        };
        let TyKind::Pi { res_ty: res_ty_1 } = pi_ty_1.to_ty().kind() else {
            panic!("pi_eq_cong(): right side of equality is not a pi type");
        };

        let motive = self.ctx().universe().scope(|arg_ty_0| {
            let arg_ty_0 = arg_ty_0.to_ty();
            arg_ty_0.ctx().universe().scope(|arg_ty_1| {
                let arg_ty_1 = arg_ty_1.to_ty();

                arg_ty_0
                .weaken_into(&arg_ty_1.ctx())
                .pi(|arg_0| arg_0.ctx().universe())
                .scope(|res_ty_0| {
                    arg_ty_1
                    .weaken_into(&res_ty_0.ctx())
                    .pi(|arg_1| arg_1.ctx().universe())
                    .scope(|res_ty_1| {
                        arg_ty_0
                        .weaken_into(&res_ty_1.ctx())
                        .pi(|arg_0| res_ty_0.app(&arg_0).to_ty())
                        .to_term()
                        .equals(
                            &arg_ty_1
                            .weaken_into(&res_ty_1.ctx())
                            .pi(|arg_1| res_ty_1.app(&arg_1).to_ty())
                            .to_term()
                        )
                        .scope(|pi_tys_eq| {
                            let arg_ty_0 = arg_ty_0.weaken_into(&pi_tys_eq.ctx());
                            let arg_ty_1 = arg_ty_1.weaken_into(&pi_tys_eq.ctx());
                            let res_ty_0 = res_ty_0.weaken_into(&pi_tys_eq.ctx());
                            let res_ty_1 = res_ty_1.weaken_into(&pi_tys_eq.ctx());
                            motive(arg_ty_0, arg_ty_1, res_ty_0, res_ty_1, pi_tys_eq)
                        })
                    })
                })
            })
        });
        let inhab = self.ctx().universe().scope(|arg_ty| {
            let arg_ty = arg_ty.to_ty();

            arg_ty
            .pi(|arg| arg.ctx().universe())
            .scope(|res_ty| {
                inhab(arg_ty.weaken_into(&res_ty.ctx()), res_ty)
            })
        });

        self
        .pi_eq_arg_injective()
        .scoped_tys_cong(
            res_ty_0.unbind(),
            res_ty_1.unbind(),
            &self.pi_eq_res_injective(),
            |arg_ty_0, arg_ty_1, _, res_ty_0, res_ty_1, _| {
                arg_ty_0
                .pi(|arg_0| res_ty_0.app(&arg_0).to_ty())
                .to_term()
                .equals(
                    &arg_ty_1
                    .pi(|arg_1| res_ty_1.app(&arg_1).to_ty())
                    .to_term()
                )
                .pi(|pi_tys_eq| {
                    motive
                    .weaken_into(&pi_tys_eq.ctx())
                    .bind(&arg_ty_0.to_term())
                    .bind(&arg_ty_1.to_term())
                    .bind(&res_ty_0.to_term())
                    .bind(&res_ty_1.to_term())
                    .bind(&pi_tys_eq)
                })
            },
            |arg_ty, res_ty| {
                let pi_ty = arg_ty.pi(|arg| res_ty.app(&arg).to_ty());

                pi_ty
                .to_term()
                .equals(&pi_ty.to_term())
                .func(|pi_tys_eq| {
                    pi_tys_eq
                    .unique_identity(
                        |pi_ty, pi_tys_eq| {
                            pi_ty
                            .equals(&pi_ty)
                            .pi(|pi_tys_eq| pi_tys_eq.ctx().universe())
                            .pi(|motive| {
                                motive
                                .app(&pi_ty.refl())
                                .to_ty()
                                .pi(|_inhab| {
                                    motive
                                    .app(&pi_tys_eq)
                                    .to_ty()
                                })
                            })
                        },
                        |pi_ty| {
                            pi_ty
                            .equals(&pi_ty)
                            .pi(|pi_tys_eq| pi_tys_eq.ctx().universe())
                            .func(|motive| {
                                motive
                                .app(&pi_ty.refl())
                                .to_ty()
                                .func(|inhab| inhab)
                            })
                        },
                    )
                    .app(
                        &pi_ty
                        .to_term()
                        .equals(&pi_ty.to_term())
                        .func(|pis_eq| {
                            motive
                            .weaken_into(&pis_eq.ctx())
                            .bind(&arg_ty.to_term())
                            .bind(&arg_ty.to_term())
                            .bind(&res_ty)
                            .bind(&res_ty)
                            .bind(&pis_eq)
                            .to_term()
                        })
                    )
                    .app(&inhab.bind(&arg_ty.to_term()).bind(&res_ty))
                })
            },
        )
        .app(self)
    }

    fn nat_eq(&self) -> Tm<S> {
        let nat_eq_ty = self.ctx().nat().scope(|n0| {
            n0.ctx().nat().scope(|n1| {
                n0
                .for_loop(
                    |n0| n0.ctx().nat().pi(|n1| n1.ctx().universe()),
                    &n0.ctx().nat().func(|n1| {
                        n1
                        .for_loop(
                            |_| n1.ctx().universe(),
                            &n1.ctx().unit_ty().to_term(),
                            |_, _| n1.ctx().never().to_term(),
                        )
                    }),
                    |n0, state| {
                        n0.ctx().nat().func(|n1| {
                            n1
                            .for_loop(
                                |_| n1.ctx().universe(),
                                &n1.ctx().never().to_term(),
                                |n1, _| state.app(&n1),
                            )
                        })
                    },
                )
                .app(&n1)
                .to_ty()
            })
        });

        self
        .cong(
            |n0, n1, _| nat_eq_ty.bind(&n0).bind(&n1),
            |n| {
                n
                .for_loop(
                    |n| nat_eq_ty.bind(&n).bind(&n),
                    &n.ctx().unit_term(),
                    |_, state| state,
                )
            },
        )
    }

    /*
    fn nat_succ_isnt_zero(&self) -> Tm<S> {
        let nat_to_ty = self.ctx().nat().scope(|nat| {
            nat
            .for_loop(
                |_| nat.ctx().universe(),
                &nat.ctx().never().to_term(),
                |_, _| nat.ctx().unit_ty().to_term(),
            )
            .to_ty()
        });

        self
        .cong(
            |nat_0, nat_1, _| {
                nat_to_ty.bind(&nat_0).pi(|_| nat_to_ty.bind(&nat_1))
            },
            |nat| nat_to_ty.bind(&nat).func(|term| term),
        )
        .app(&self.ctx().unit_term())
    }
    */

    fn case_eq(&self) -> Tm<S> {
        self
        .cong(
            |x0, x1, _| {
                x0
                .case(
                    |elim| elim.ctx().universe(),
                    |lhs_0| {
                        x1
                        .weaken_into(&lhs_0.ctx())
                        .case(
                            |elim| elim.ctx().universe(),
                            |lhs_1| lhs_0.equals(&lhs_1).to_term(),
                            |rhs_1| rhs_1.ctx().never().to_term(),
                        )
                    },
                    |rhs_0| {
                        x1
                        .weaken_into(&rhs_0.ctx())
                        .case(
                            |elim| elim.ctx().universe(),
                            |lhs_1| lhs_1.ctx().never().to_term(),
                            |rhs_1| rhs_0.equals(&rhs_1).to_term(),
                        )
                    },
                )
                .to_ty()
            },
            |x| x.case(
                |x0| {
                    x0
                    .case(
                        |elim| elim.ctx().universe(),
                        |lhs_0| {
                            x0
                            .weaken_into(&lhs_0.ctx())
                            .case(
                                |elim| elim.ctx().universe(),
                                |lhs_1| lhs_0.equals(&lhs_1).to_term(),
                                |rhs_1| rhs_1.ctx().never().to_term(),
                            )
                        },
                        |rhs_0| {
                            x0
                            .weaken_into(&rhs_0.ctx())
                            .case(
                                |elim| elim.ctx().universe(),
                                |lhs_1| lhs_1.ctx().never().to_term(),
                                |rhs_1| rhs_0.equals(&rhs_1).to_term(),
                            )
                        },
                    )
                    .to_ty()
                },
                |lhs| lhs.refl(),
                |rhs| rhs.refl(),
            )
        )
    }

    fn pair_eq(
        &self,
        tail_ty: impl FnOnce(Tm<S>) -> Ty<S>,
        tail_0: &Tm<S>,
        tail_1: &Tm<S>,
        tail_eq: &Tm<S>,
    ) -> Tm<S> {
        let TyKind::Equal { eq_term_0, .. } = self.ty().kind() else {
            panic!();
        };
        let head_ty = eq_term_0.ty();
        let tail_ty = head_ty.scope(tail_ty);

        self
        .cong(
            |head_0, head_1, head_eq| {
                tail_ty
                .bind(&head_0)
                .pi(|tail_0| {
                    tail_ty
                    .weaken_into(&tail_0.ctx())
                    .bind(&head_1)
                    .pi(|tail_1| {
                        head_eq
                        .map_eq(|head| tail_ty.bind(&head).to_term())
                        .heterogeneous_equal(&tail_0, &tail_1)
                        .pi(|tail_eq| {
                            head_0
                            .weaken_into(&tail_eq.ctx())
                            .pair(
                                |head| tail_ty.bind(&head),
                                &tail_0,
                            )
                            .equals(
                                &head_1
                                .weaken_into(&tail_eq.ctx())
                                .pair(
                                    |head| tail_ty.bind(&head),
                                    &tail_1,
                                )
                            )
                        })
                    })
                })
            },
            |head| {
                tail_ty
                .bind(&head)
                .func(|tail_0| {
                    tail_ty
                    .weaken_into(&tail_0.ctx())
                    .bind(&head)
                    .func(|tail_1| {
                        tail_0
                        .equals(&tail_1)
                        .func(|tail_eq| {
                            tail_eq
                            .cong(
                                |tail_0, tail_1, tail_eq| {
                                    head
                                    .weaken_into(&tail_eq.ctx())
                                    .pair(
                                        |head| tail_ty.bind(&head),
                                        &tail_0,
                                    )
                                    .equals(
                                        &head
                                        .weaken_into(&tail_eq.ctx())
                                        .pair(
                                            |head| tail_ty.bind(&head),
                                            &tail_1,
                                        )
                                    )
                                },
                                |tail| {
                                    head
                                    .weaken_into(&tail.ctx())
                                    .pair(
                                        |head| tail_ty.bind(&head),
                                        &tail,
                                    )
                                    .refl()
                                },
                            )
                        })
                    })
                })
            },
        )
        .app(&tail_0)
        .app(&tail_1)
        .app(&tail_eq)
    }

    fn nat_succ_injective(&self) -> Tm<S> {
        self
        .cong(
            |nat_0, nat_1, nat_eq| {
                nat_0
                .for_loop(
                    |nat_0| nat_0.ctx().universe(),
                    &nat_1.for_loop(
                        |nat_1| nat_1.ctx().universe(),
                        &nat_eq.ctx().zero().equals(&nat_eq.ctx().zero()).to_term(),
                        |_, state| state.ctx().never().to_term(),
                    ),
                    |nat_0, _| {
                        nat_1
                        .for_loop(
                            |nat_1| nat_1.ctx().universe(),
                            &nat_0.ctx().never().to_term(),
                            |nat_1, _| nat_0.equals(&nat_1).to_term(),
                        )
                    },
                )
                .to_ty()
            },
            |nat| {
                nat
                .for_loop(
                    |nat| {
                        nat
                        .for_loop(
                            |nat_0| nat_0.ctx().universe(),
                            &nat.for_loop(
                                |nat_1| nat_1.ctx().universe(),
                                &nat.ctx().zero().equals(&nat.ctx().zero()).to_term(),
                                |_, state| state.ctx().never().to_term(),
                            ),
                            |nat_0, _| {
                                nat
                                .for_loop(
                                    |nat_1| nat_1.ctx().universe(),
                                    &nat_0.ctx().never().to_term(),
                                    |nat_1, _| nat_0.equals(&nat_1).to_term(),
                                )
                            },
                        )
                        .to_ty()
                    },
                    &nat.ctx().zero().refl(),
                    |nat, _| nat.refl(),
                )
            },
        )
    }

    fn nat_succs_injective(&self, succs: impl Into<BigUint>) -> Tm<S> {
        let mut counter = succs.into();
        let mut ret = self.clone();
        while !counter.is_zero() {
            ret = ret.nat_succ_injective();
            counter -= 1u32;
        }
        ret
    }

    fn map_eq(
        &self,
        func: impl FnOnce(Tm<S>) -> Tm<S>,
    ) -> Tm<S> {
        let TyKind::Equal { eq_term_0, .. } = self.ty().kind() else {
            panic!("not an equality");
        };
        let eq_ty = eq_term_0.ty();
        let scope = eq_ty.scope(func);
        
        self
        .cong(
            |x0, x1, _eq| {
                scope.bind(&x0).equals(&scope.bind(&x1))
            },
            |x| scope.bind(&x).refl(),
        )
    }

    fn map_eq_dependent(
        &self,
        func: impl FnOnce(Tm<S>) -> Tm<S>,
    ) -> Tm<S> {
        let TyKind::Equal { eq_term_0, .. } = self.ty().kind() else {
            panic!("not an equality");
        };
        let eq_ty = eq_term_0.ty();
        let scope = eq_ty.scope(func);
        let scope_ty = scope.map(|_, term| term.ty());
        
        self
        .cong(
            |x0, x1, eq| {
                scope_ty
                .bind_eq(&eq)
                .heterogeneous_equal(
                    &scope.bind(&x0),
                    &scope.bind(&x1),
                )
            },
            |x| scope.bind(&x).refl(),
        )
    }

    fn equality_contractible(&self, other: &Tm<S>) -> Tm<S> {
        self
        .cong(
            |val_0, val_1, val_eq_0| {
                val_0
                .equals(&val_1)
                .pi(|val_eq_1| {
                    val_eq_0.equals(&val_eq_1)
                })
            },
            |val| {
                val
                .equals(&val)
                .func(|val_eq| {
                    val_eq
                    .unique_identity(
                        |val, val_eq| val.refl().equals(&val_eq),
                        |val| val.refl().refl(),
                    )
                })
            },
        )
        .app(other)
    }

    fn equals_refl(&self) -> Tm<S> {
        self
        .unique_identity(
            |eq_term, elim| elim.equals(&eq_term.refl()),
            |eq_term| eq_term.refl().refl(),
        )
    }

    fn try_find_alternate_term(&self) -> Option<(Tm<S>, Scope<S, Tm<S>>)> {
        match self.kind() {
            TmKind::Stuck { .. } => {
                // TODO
            },
            TmKind::User { .. } => (),
            TmKind::Type { .. } => {
                // TODO
            },
            TmKind::Zero => {
                //let alt_term = self.ctx().nat_constant(1);
                // TODO
            },
            TmKind::Succs { .. } => {
                // TODO
            },

            TmKind::Refl { .. } => (),
            TmKind::Unit => (),

            TmKind::InjLhs { lhs_term, rhs_ty } => {
                if let Some((lhs_alt_term, lhs_scope)) = lhs_term.try_find_alternate_term() {
                    let alt_term = lhs_alt_term.inj_lhs(&rhs_ty);
                    let scope = self.equals(&alt_term).scope(|eq| {
                        lhs_scope.bind(&eq.case_eq())
                    });
                    return Some((alt_term, scope));
                }
                if let Some(rhs_term) = rhs_ty.try_find_arbitrary_term() {
                    let alt_term = rhs_term.inj_rhs(&lhs_term.ty());
                    let scope = self.equals(&alt_term).scope(|eq| eq.case_eq());
                    return Some((alt_term, scope));
                }
            },

            TmKind::InjRhs { rhs_term, lhs_ty } => {
                if let Some((rhs_alt_term, rhs_scope)) = rhs_term.try_find_alternate_term() {
                    let alt_term = rhs_alt_term.inj_rhs(&lhs_ty);
                    let scope = self.equals(&alt_term).scope(|eq| {
                        rhs_scope.bind(&eq.case_eq())
                    });
                    return Some((alt_term, scope));
                }
                if let Some(lhs_term) = lhs_ty.try_find_arbitrary_term() {
                    let alt_term = lhs_term.inj_lhs(&rhs_term.ty());
                    let scope = self.equals(&alt_term).scope(|eq| eq.case_eq());
                    return Some((alt_term, scope));
                }
            },

            TmKind::Pair { tail_ty, head_term, tail_term } => {
                if let Some((tail_alt_term, tail_scope)) = tail_term.try_find_alternate_term() {
                    let alt_term = head_term.pair(|head_term| tail_ty.bind(&head_term), &tail_alt_term);
                    let scope = self.equals(&alt_term).scope(|eq| {
                        tail_scope
                        .bind(&eq.map_eq(|pair_term| pair_term.proj_tail()))
                    });
                    return Some((alt_term, scope));
                }
                if let Some((head_alt_term, head_scope)) = head_term.try_find_alternate_term() {
                    if let Some(tail_ty) = tail_ty.try_strengthen() {
                        let alt_term = head_alt_term.pair(|_| tail_ty, &tail_term);
                        let scope = self.equals(&alt_term).scope(|eq| {
                            head_scope
                            .bind(&eq.map_eq(|pair_term| pair_term.proj_head()))
                        });
                        return Some((alt_term, scope));
                    }
                    if let Some(tail_alt_term) = tail_ty.bind(&head_alt_term).try_find_arbitrary_term() {
                        let alt_term = head_alt_term.pair(|head_term| tail_ty.bind(&head_term), &tail_alt_term);
                        let scope = self.equals(&alt_term).scope(|eq| {
                            head_scope
                            .bind(&eq.map_eq(|pair_term| pair_term.proj_head()))
                        });
                        return Some((alt_term, scope));
                    }
                }
            },

            TmKind::Func { res_term } => {
                if let Some((res_alt_term, res_scope)) = res_term.map_out(|_, res_term| {
                    res_term.try_find_alternate_term()
                }) {
                    let res_alt_term = Scope::new(res_alt_term);
                    let res_scope = Scope::new(res_scope);

                    if let Some(arg_term) = res_term.var_ty().try_find_arbitrary_term() {
                        let alt_term = res_alt_term.to_func();
                        let scope = self.equals(&alt_term).scope(|eq| {
                            res_scope
                            .bind(&arg_term)
                            .bind(&eq.map_eq(|func| func.app(&arg_term)))
                        });
                        return Some((alt_term, scope));
                    }
                }
            },
        }
        None
    }

    fn try_prove_apart(&self, other: &Tm<S>) -> Option<Uninhabited<S>> {
        match self.ty().kind() {
            TyKind::User { .. } => None,
            TyKind::Stuck { .. } => None, // TODO
            TyKind::Universe => {
                match self.to_ty().try_prove_uninhabited() {
                    Some(uninhabited) => {
                        let term = other.to_ty().try_find_arbitrary_term()?;
                        Some(Uninhabited::new(
                            &self.equals(other),
                            |eq| uninhabited.contradiction(&eq.symmetry().transport(&term)),
                        ))
                    },
                    None => {
                        let term = self.to_ty().try_find_arbitrary_term()?;
                        let uninhabited = other.to_ty().try_prove_uninhabited()?;
                        Some(Uninhabited::new(
                            &self.equals(other),
                            |eq| uninhabited.contradiction(&eq.transport(&term)),
                        ))
                    },
                }
            },
            TyKind::Nat => {
                // TODO
                None
            },
            TyKind::Equal { .. } => None,
            TyKind::Never => {
                Some(Uninhabited::new(
                    &self.equals(other),
                    |_| self.clone(),
                ))
            },
            TyKind::Unit => None,
            TyKind::Sum { .. } => {
                match self.kind() {
                    TmKind::Stuck { .. } => None,
                    TmKind::InjLhs { lhs_term: lhs_term_0, rhs_ty: _ } => match other.kind() {
                        TmKind::Stuck { .. } => None,
                        TmKind::InjLhs { lhs_term: lhs_term_1, rhs_ty: _ } => {
                            let lhs_apart = lhs_term_0.try_prove_apart(&lhs_term_1)?;
                            Some(Uninhabited::new(
                                &self.equals(other),
                                |eq| lhs_apart.contradiction(&eq.case_eq())
                            ))
                        },
                        TmKind::InjRhs { .. } => {
                            Some(Uninhabited::new(
                                &self.equals(other),
                                |eq| eq.case_eq(),
                            ))
                        },
                        _ => unreachable!(),
                    },
                    TmKind::InjRhs { rhs_term: rhs_term_0, lhs_ty: _ } => match other.kind() {
                        TmKind::Stuck { .. } => None,
                        TmKind::InjLhs { .. } => {
                            Some(Uninhabited::new(
                                &self.equals(other),
                                |eq| eq.case_eq(),
                            ))
                        },
                        TmKind::InjRhs { rhs_term: rhs_term_1, lhs_ty: _ } => {
                            let rhs_apart = rhs_term_0.try_prove_apart(&rhs_term_1)?;
                            Some(Uninhabited::new(
                                &self.equals(other),
                                |eq| rhs_apart.contradiction(&eq.case_eq())
                            ))
                        },
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                }
            },
            TyKind::Sigma { tail_ty } => {
                match self.proj_head().try_prove_apart(&other.proj_head()) {
                    Some(head_apart) => {
                        Some(Uninhabited::new(
                            &self.equals(other),
                            |eq| head_apart.contradiction(
                                &eq.map_eq(|pair_term| pair_term.proj_head())
                            ),
                        ))
                    },
                    None => {
                        if tail_ty.bind(&self.proj_head()) == tail_ty.bind(&other.proj_head()) {
                            let tail_apart = self.proj_tail().try_prove_apart(&other.proj_tail())?;
                            Some(Uninhabited::new(
                                &self.equals(other),
                                |eq| tail_apart.contradiction(
                                    &eq.map_eq(|pair_term| pair_term.proj_tail())
                                ),
                            ))
                        } else {
                            None
                        }
                    },
                }
            },
            TyKind::Pi { res_ty } => {
                let arg_term = res_ty.var_ty().try_find_arbitrary_term()?;
                let res_term_0 = self.app(&arg_term);
                let res_term_1 = other.app(&arg_term);
                let res_apart = res_term_0.try_prove_apart(&res_term_1)?;
                Some(Uninhabited::new(
                    &self.equals(other),
                    |eq| res_apart.contradiction(
                        &eq.map_eq(|func| func.app(&arg_term))
                    ),
                ))
            },
        }
    }

    fn to_iso(&self) -> Iso<S> {
        let TyKind::Equal { eq_term_0, eq_term_1 } = self.ty().kind() else {
            panic!();
        };
        let ty_0 = eq_term_0.to_ty();
        let ty_1 = eq_term_1.to_ty();
        Iso::new(
            &ty_0,
            &ty_1,
            |term_0| self.transport(&term_0),
            |term_1| self.symmetry().transport(&term_1),
            |term_0| self.cong(
                |_, _, ty_eq| {
                    ty_eq
                    .symmetry()
                    .transport(&ty_eq.transport(&term_0))
                    .equals(&term_0)
                },
                |_| term_0.refl(),
            ),
            |term_1| self.cong(
                |_, _, ty_eq| {
                    ty_eq
                    .transport(&ty_eq.symmetry().transport(&term_1))
                    .equals(&term_1)
                },
                |_| term_1.refl(),
            ),
        )
    }

    fn epi_to_unit(&self) -> Epi<S> {
        Epi::new(
            &self.ty(),
            &self.ctx().unit_ty(),
            |term| term.ctx().unit_term(),
            |_| self.clone(),
            |term| term.refl(),
        )
    }

    fn pointed(&self) -> Tm<S> {
        self.ty().to_term().pair(|ty| ty.to_ty(), self)
    }
}

