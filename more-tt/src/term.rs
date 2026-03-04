use crate::priv_prelude::*;

#[extension(pub trait TmExt)]
impl<S: Scheme> Tm<S> {
    fn symmetry(&self) -> Tm<S> {
        let (val_0, val_1) = self.ty().unwrap_equal();

        closed::symmetry()
        .app(&val_0.ty().to_term())
        .app(&val_0)
        .app(&val_1)
        .app(self)
    }

    fn transitivity(&self, other: &Tm<S>) -> Tm<S> {
        let (eq_0, eq_1) = Ctx::into_common_ctx((self, other));
        let (val_0, val_1_0) = eq_0.ty().unwrap_equal();
        let (val_1_1, val_2) = eq_1.ty().unwrap_equal();
        let Some(val_1) = as_equal(&val_1_0, &val_1_1) else {
            panic!("\
                transitivity(): common endpoint of self and other does not match.
                self.eq_term_1: {:?}\n\
                other.eq_term_0: {:?}",
                val_1_0,
                val_1_1,
            );
        };
        let ty = val_0.ty();

        closed::transitivity()
        .app(&ty.to_term())
        .app(&val_0)
        .app(&val_1)
        .app(&val_2)
        .app(&eq_0)
        .app(&eq_1)
    }

    fn transport(&self, term: &Tm<S>) -> Tm<S> {
        let (ty_0, ty_1) = self.ty().unwrap_equal();

        closed::transport()
        .app(&ty_0)
        .app(&ty_1)
        .app(self)
        .app(term)
    }

    fn heterogeneous_equal(&self, term_0: &Tm<S>, term_1: &Tm<S>) -> Ty<S> {
        let (ty_0, ty_1) = self.ty().unwrap_equal();

        closed::heterogeneous_equal()
        .app(&ty_0)
        .app(&ty_1)
        .app(self)
        .app(term_0)
        .app(term_1)
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
        closed::heterogeneous_transitivity()
        .app(&term_0.ty().to_term())
        .app(&term_1.ty().to_term())
        .app(&term_2.ty().to_term())
        .app(tys_eq_0)
        .app(tys_eq_1)
        .app(term_0)
        .app(term_1)
        .app(term_2)
        .app(terms_eq_0)
        .app(terms_eq_1)
    }

    /*
    fn scoped_tys_equal(
        &self,
        body_ty_0: impl FnOnce(Tm<S>) -> Ty<S>,
        body_ty_1: impl FnOnce(Tm<S>) -> Ty<S>,
    ) -> Ty<S> {
        let (var_ty_0, var_ty_1) = self.ty().unwrap_equal();
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
    */

    fn scoped_tys_equal_contractible(
        var_name_eq: &Tm<S>,
        var_ty_eq: &Tm<S>,
        body_ty_0: impl FnOnce(Tm<S>) -> Ty<S>,
        body_ty_1: impl FnOnce(Tm<S>) -> Ty<S>,
        scoped_tys_eq_0: &Tm<S>,
        scoped_tys_eq_1: &Tm<S>,
    ) -> Tm<S> {
        same_ctx!(var_name_eq, var_ty_eq, scoped_tys_eq_0, scoped_tys_eq_1);

        let (var_ty_0, var_ty_1) = var_ty_eq.ty().unwrap_equal();
        let var_ty_0 = var_ty_0.to_ty();
        let var_ty_1 = var_ty_1.to_ty();

        let body_ty_0 = var_ty_0.scope(body_ty_0);
        let body_ty_1 = var_ty_1.scope(body_ty_1);

        let scoped_ty_0_name = S::name_from_str("scoped_ty_0");
        let scoped_ty_1_name = S::name_from_str("scoped_ty_1");
        let scoped_tys_eq_0_name = S::name_from_str("scoped_tys_eq_0");
        let scoped_tys_eq_1_name = S::name_from_str("scoped_tys_eq_1");

        var_name_eq
        .cong(
            |_, _, var_name_eq| {
                Ty::scoped_tys_equal(
                    &var_name_eq,
                    &var_ty_eq,
                    body_ty_0.unbind(),
                    body_ty_1.unbind(),
                )
                .pi(&scoped_tys_eq_0_name, |scoped_tys_eq_0| {
                    Ty::scoped_tys_equal(
                        &var_name_eq,
                        &var_ty_eq,
                        body_ty_0.unbind(),
                        body_ty_1.unbind(),
                    )
                    .weaken_into(&scoped_tys_eq_0.ctx())
                    .pi(&scoped_tys_eq_1_name, |scoped_tys_eq_1| {
                        scoped_tys_eq_0
                        .equals(&scoped_tys_eq_1)
                    })
                })
            },
            |var_name| {
                let var_name = var_name.to_name();

                var_ty_eq
                .weaken_into(&var_name.ctx())
                .cong(
                    |var_ty_0, var_ty_1, var_ty_eq| {
                        let var_ty_0 = var_ty_0.to_ty();
                        let var_ty_1 = var_ty_1.to_ty();

                        var_ty_0
                        .pi(&var_name, |var| var.ctx().universe())
                        .pi(&scoped_ty_0_name, |body_ty_0| {
                            var_ty_1
                            .weaken_into(&body_ty_0.ctx())
                            .pi(&var_name, |var| var.ctx().universe())
                            .pi(&scoped_ty_1_name, |body_ty_1| {
                                same_ctx!(&var_name, &var_ty_eq, &body_ty_0, &body_ty_1);

                                Ty::scoped_tys_equal(
                                    &var_name.to_term().refl(),
                                    &var_ty_eq,
                                    |var| body_ty_0.app(&var).to_ty(),
                                    |var| body_ty_1.app(&var).to_ty(),
                                )
                                .pi(&scoped_tys_eq_0_name, |scoped_tys_eq_0| {
                                    same_ctx!(
                                        &var_name,
                                        &var_ty_eq,
                                        &body_ty_0,
                                        &body_ty_1,
                                        &scoped_tys_eq_0,
                                    );

                                    Ty::scoped_tys_equal(
                                        &var_name.to_term().refl(),
                                        &var_ty_eq,
                                        |var| body_ty_0.app(&var).to_ty(),
                                        |var| body_ty_1.app(&var).to_ty(),
                                    )
                                    .weaken_into(&scoped_tys_eq_0.ctx())
                                    .pi(&scoped_tys_eq_1_name, |scoped_tys_eq_1| {
                                        scoped_tys_eq_0
                                        .equals(&scoped_tys_eq_1)
                                    })
                                })
                            })
                        })
                    },
                    |var_ty| {
                        let var_ty = var_ty.to_ty();

                        var_ty
                        .pi(&var_name, |var| var.ctx().universe())
                        .func(&scoped_ty_0_name, |body_ty_0| {
                            var_ty
                            .weaken_into(&body_ty_0.ctx())
                            .pi(&var_name, |var| var.ctx().universe())
                            .func(&scoped_ty_1_name, |body_ty_1| {
                                same_ctx!(&var_name, &var_ty, &body_ty_0, &body_ty_1);

                                var_ty
                                .func(&var_name, |var| body_ty_0.app(&var))
                                .equals(
                                    &var_ty
                                    .func(&var_name, |var| body_ty_1.app(&var))
                                )
                                .func(&scoped_tys_eq_0_name, |scoped_tys_eq_0| {
                                    same_ctx!(
                                        &var_name,
                                        &var_ty,
                                        &body_ty_0,
                                        &body_ty_1,
                                        &scoped_tys_eq_0,
                                    );

                                    var_ty
                                    .func(&var_name, |var| body_ty_0.app(&var))
                                    .equals(
                                        &var_ty
                                        .func(&var_name, |var| body_ty_1.app(&var))
                                    )
                                    .weaken_into(&scoped_tys_eq_0.ctx())
                                    .func(&scoped_tys_eq_1_name, |scoped_tys_eq_1| {
                                        scoped_tys_eq_0
                                        .equality_contractible(&scoped_tys_eq_1)
                                    })
                                })
                            })
                        })
                    },
                )
                .app(&var_ty_0.func(&var_name, |var| body_ty_0.bind(&var).to_term()))
                .app(&var_ty_1.func(&var_name, |var| body_ty_1.bind(&var).to_term()))
            },
        )
        .app(&scoped_tys_eq_0)
        .app(&scoped_tys_eq_1)
    }


    /*
    fn scoped_tys_cong(
        &self,
        body_ty_0: impl FnOnce(Tm<S>) -> Ty<S>,
        body_ty_1: impl FnOnce(Tm<S>) -> Ty<S>,
        body_tys_eq: &Tm<S>,
        motive: impl FnOnce(Ty<S>, Ty<S>, Tm<S>, Tm<S>, Tm<S>, Tm<S>) -> Ty<S>,
        inhab: impl FnOnce(Ty<S>, Tm<S>) -> Tm<S>,
    ) -> Tm<S> {
        let (var_ty_0, var_ty_1) = self.ty().unwrap_equal();
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
    */

    fn sigma_eq_cong(
        &self,
        motive: impl FnOnce(
            Name<S>,
            Name<S>,
            Ty<S>,
            Ty<S>,
            Tm<S>,
            Tm<S>,
            Tm<S>,
        ) -> Ty<S>,
        inhab: impl FnOnce(
            Name<S>,
            Ty<S>,
            Tm<S>,
        ) -> Tm<S>,
    ) -> Tm<S> {
        let (sigma_ty_0, sigma_ty_1) = self.ty().unwrap_equal();
        let (head_name_0, tail_ty_0) = sigma_ty_0.to_ty().unwrap_sigma();
        let (head_name_1, tail_ty_1) = sigma_ty_1.to_ty().unwrap_sigma();
        let head_ty_0 = tail_ty_0.var_ty();
        let head_ty_1 = tail_ty_1.var_ty();

        let head_name_0_name = S::name_from_str("head_name_0");
        let head_name_1_name = S::name_from_str("head_name_1");
        let head_ty_0_name = S::name_from_str("Head0");
        let head_ty_1_name = S::name_from_str("Head1");
        let tail_ty_0_name = S::name_from_str("Tail0");
        let tail_ty_1_name = S::name_from_str("Tail1");
        let sigma_eq_name = S::name_from_str("sigma_eq");

        let head_name_name = S::name_from_str("head_name");
        let head_ty_name = S::name_from_str("Head");
        let tail_ty_name = S::name_from_str("Tail");

        closed::sigma_eq_cong()
        .app(
            &self
            .ctx()
            .name()
            .func(&head_name_0_name, |head_name_0| {
                let head_name_0 = head_name_0.to_name();

                head_name_0
                .ctx()
                .name()
                .func(&head_name_1_name, |head_name_1| {
                    let head_name_1 = head_name_1.to_name();

                    head_name_1
                    .ctx()
                    .universe()
                    .func(&head_ty_0_name, |head_ty_0| {
                        let head_ty_0 = head_ty_0.to_ty();

                        head_ty_0
                        .ctx()
                        .universe()
                        .func(&head_ty_1_name, |head_ty_1| {
                            let head_ty_1 = head_ty_1.to_ty();

                            head_ty_0
                            .weaken_into(&head_ty_1.ctx())
                            .pi(&head_name_0, |head| head.ctx().universe())
                            .func(&tail_ty_0_name, |tail_ty_0| {
                                head_ty_1
                                .weaken_into(&tail_ty_0.ctx())
                                .pi(&head_name_1, |head| head.ctx().universe())
                                .func(&tail_ty_1_name, |tail_ty_1| {
                                    head_ty_0
                                    .weaken_into(&tail_ty_1.ctx())
                                    .sigma(&head_name_0, |head| {
                                        tail_ty_0.app(&head).to_ty()
                                    })
                                    .to_term()
                                    .equals(
                                        &head_ty_1
                                        .weaken_into(&tail_ty_1.ctx())
                                        .sigma(&head_name_1, |head| {
                                            tail_ty_1.app(&head).to_ty()
                                        })
                                        .to_term()
                                    )
                                    .func(&sigma_eq_name, |sigma_eq| {
                                        let head_name_0 = head_name_0.weaken_into(&sigma_eq.ctx());
                                        let head_name_1 = head_name_1.weaken_into(&sigma_eq.ctx());
                                        let head_ty_0 = head_ty_0.weaken_into(&sigma_eq.ctx());
                                        let head_ty_1 = head_ty_1.weaken_into(&sigma_eq.ctx());
                                        let tail_ty_0 = tail_ty_0.weaken_into(&sigma_eq.ctx());
                                        let tail_ty_1 = tail_ty_1.weaken_into(&sigma_eq.ctx());
                                        motive(
                                            head_name_0,
                                            head_name_1,
                                            head_ty_0,
                                            head_ty_1,
                                            tail_ty_0,
                                            tail_ty_1,
                                            sigma_eq,
                                        )
                                        .to_term()
                                    })
                                })
                            })
                        })
                    })
                })
            })
        )
        .app(
            &self
            .ctx()
            .name()
            .func(&head_name_name, |head_name| {
                let head_name = head_name.to_name();

                head_name
                .ctx()
                .universe()
                .func(&head_ty_name, |head_ty| {
                    let head_ty = head_ty.to_ty();

                    head_ty
                    .pi(&head_name, |head| head.ctx().universe())
                    .func(&tail_ty_name, |tail_ty| {
                        let head_name = head_name.weaken_into(&tail_ty.ctx());
                        let head_ty = head_ty.weaken_into(&tail_ty.ctx());

                        inhab(head_name, head_ty, tail_ty)
                    })
                })
            })
        )
        .app(&head_name_0.to_term())
        .app(&head_name_1.to_term())
        .app(&head_ty_0.to_term())
        .app(&head_ty_1.to_term())
        .app(&head_ty_0.func(&head_name_0, |head| tail_ty_0.bind(&head).to_term()))
        .app(&head_ty_1.func(&head_name_1, |head| tail_ty_1.bind(&head).to_term()))
        .app(self)
    }

    fn pi_eq_cong(
        &self,
        motive: impl FnOnce(
            Name<S>,
            Name<S>,
            Ty<S>,
            Ty<S>,
            Tm<S>,
            Tm<S>,
            Tm<S>,
        ) -> Ty<S>,
        inhab: impl FnOnce(
            Name<S>,
            Ty<S>,
            Tm<S>,
        ) -> Tm<S>,
    ) -> Tm<S> {
        let (pi_ty_0, pi_ty_1) = self.ty().unwrap_equal();
        let (arg_name_0, res_ty_0) = pi_ty_0.to_ty().unwrap_pi();
        let (arg_name_1, res_ty_1) = pi_ty_1.to_ty().unwrap_pi();
        let arg_ty_0 = res_ty_0.var_ty();
        let arg_ty_1 = res_ty_1.var_ty();

        let arg_name_0_name = S::name_from_str("arg_name_0");
        let arg_name_1_name = S::name_from_str("arg_name_1");
        let arg_ty_0_name = S::name_from_str("Arg0");
        let arg_ty_1_name = S::name_from_str("Arg1");
        let res_ty_0_name = S::name_from_str("Res0");
        let res_ty_1_name = S::name_from_str("Res1");
        let pi_eq_name = S::name_from_str("pi_eq");

        let arg_name_name = S::name_from_str("arg_name");
        let arg_ty_name = S::name_from_str("Arg");
        let res_ty_name = S::name_from_str("Res");

        closed::pi_eq_cong()
        .app(
            &self
            .ctx()
            .name()
            .func(&arg_name_0_name, |arg_name_0| {
                let arg_name_0 = arg_name_0.to_name();

                arg_name_0
                .ctx()
                .name()
                .func(&arg_name_1_name, |arg_name_1| {
                    let arg_name_1 = arg_name_1.to_name();

                    arg_name_1
                    .ctx()
                    .universe()
                    .func(&arg_ty_0_name, |arg_ty_0| {
                        let arg_ty_0 = arg_ty_0.to_ty();

                        arg_ty_0
                        .ctx()
                        .universe()
                        .func(&arg_ty_1_name, |arg_ty_1| {
                            let arg_ty_1 = arg_ty_1.to_ty();

                            arg_ty_0
                            .weaken_into(&arg_ty_1.ctx())
                            .pi(&arg_name_0, |arg| arg.ctx().universe())
                            .func(&res_ty_0_name, |res_ty_0| {
                                arg_ty_1
                                .weaken_into(&res_ty_0.ctx())
                                .pi(&arg_name_1, |arg| arg.ctx().universe())
                                .func(&res_ty_1_name, |res_ty_1| {
                                    arg_ty_0
                                    .weaken_into(&res_ty_1.ctx())
                                    .pi(&arg_name_0, |arg| {
                                        res_ty_0.app(&arg).to_ty()
                                    })
                                    .to_term()
                                    .equals(
                                        &arg_ty_1
                                        .weaken_into(&res_ty_1.ctx())
                                        .pi(&arg_name_1, |arg| {
                                            res_ty_1.app(&arg).to_ty()
                                        })
                                        .to_term()
                                    )
                                    .func(&pi_eq_name, |pi_eq| {
                                        let arg_name_0 = arg_name_0.weaken_into(&pi_eq.ctx());
                                        let arg_name_1 = arg_name_1.weaken_into(&pi_eq.ctx());
                                        let arg_ty_0 = arg_ty_0.weaken_into(&pi_eq.ctx());
                                        let arg_ty_1 = arg_ty_1.weaken_into(&pi_eq.ctx());
                                        let res_ty_0 = res_ty_0.weaken_into(&pi_eq.ctx());
                                        let res_ty_1 = res_ty_1.weaken_into(&pi_eq.ctx());
                                        motive(
                                            arg_name_0,
                                            arg_name_1,
                                            arg_ty_0,
                                            arg_ty_1,
                                            res_ty_0,
                                            res_ty_1,
                                            pi_eq,
                                        )
                                        .to_term()
                                    })
                                })
                            })
                        })
                    })
                })
            })
        )
        .app(
            &self
            .ctx()
            .name()
            .func(&arg_name_name, |arg_name| {
                let arg_name = arg_name.to_name();

                arg_name
                .ctx()
                .universe()
                .func(&arg_ty_name, |arg_ty| {
                    let arg_ty = arg_ty.to_ty();

                    arg_ty
                    .pi(&arg_name, |arg| arg.ctx().universe())
                    .func(&res_ty_name, |res_ty| {
                        let arg_name = arg_name.weaken_into(&res_ty.ctx());
                        let arg_ty = arg_ty.weaken_into(&res_ty.ctx());

                        inhab(arg_name, arg_ty, res_ty)
                    })
                })
            })
        )
        .app(&arg_name_0.to_term())
        .app(&arg_name_1.to_term())
        .app(&arg_ty_0.to_term())
        .app(&arg_ty_1.to_term())
        .app(&arg_ty_0.func(&arg_name_0, |arg| res_ty_0.bind(&arg).to_term()))
        .app(&arg_ty_1.func(&arg_name_1, |arg| res_ty_1.bind(&arg).to_term()))
        .app(self)
    }

    fn nat_eq(&self) -> Tm<S> {
        let n1_name = S::name_from_str("other_nat");
        let nat_eq_ty = self.ctx().nat().scope(|n0| {
            n0.ctx().nat().scope(|n1| {
                n0
                .for_loop(
                    |n0| n0.ctx().nat().pi(&n1_name, |n1| n1.ctx().universe()),
                    &n0.ctx().nat().func(&n1_name, |n1| {
                        n1
                        .for_loop(
                            |_| n1.ctx().universe(),
                            &n1.ctx().unit_ty().to_term(),
                            |_, _| n1.ctx().never().to_term(),
                        )
                    }),
                    |n0, state| {
                        n0.ctx().nat().func(&n1_name, |n1| {
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

    fn nat_succ_isnt_zero(&self) -> Tm<S> {
        let fin_name = S::name_from_str("Fin");
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
                nat_to_ty.bind(&nat_0).pi(&fin_name, |_| nat_to_ty.bind(&nat_1))
            },
            |nat| nat_to_ty.bind(&nat).func(&fin_name, |term| term),
        )
        .app(&self.ctx().unit_term())
    }

    fn case_eq(&self) -> Tm<S> {
        let (eq_term_0, eq_term_1) = self.ty().unwrap_equal();
        let (lhs_name, lhs_ty, rhs_ty) = eq_term_0.ty().unwrap_sum();

        closed::case_eq()
        .app(&lhs_name.to_term())
        .app(&lhs_ty.to_term())
        .app(&rhs_ty.to_term())
        .app(&eq_term_0)
        .app(&eq_term_1)
        .app(self)
    }

    fn pair_eq(
        &self,
        head_name: &Name<S>,
        tail_ty: impl FnOnce(Tm<S>) -> Ty<S>,
        tail_0: &Tm<S>,
        tail_1: &Tm<S>,
        tail_eq: &Tm<S>,
    ) -> Tm<S> {
        let (head_name, head_eq, tail_0, tail_1, tail_eq) = Ctx::into_common_ctx((
            head_name, self, tail_0, tail_1, tail_eq,
        ));
        let (head_0, head_1) = head_eq.ty().unwrap_equal();
        let head_ty = head_0.ty();
        let tail_ty = head_ty.scope(tail_ty);

        debug_assert_eq!(tail_0.ty(), tail_ty.bind(&head_0));
        debug_assert_eq!(tail_1.ty(), tail_ty.bind(&head_1));
        debug_assert_eq!(
            tail_eq.ty(),
            tail_ty
            .bind_eq(&head_eq)
            .heterogeneous_equal(&tail_0, &tail_1),
        );

        closed::pair_eq()
        .app(&head_name.to_term())
        .app(&head_ty.to_term())
        .app(&head_ty.func(&head_name, |head| tail_ty.bind(&head).to_term()))
        .app(&head_0)
        .app(&head_1)
        .app(&head_eq)
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
        let (val_0, val_1) = self.ty().unwrap_equal();
        let val_name = S::name_from_str("map_eq_val");
        let arg_ty = val_0.ty();
        let func = arg_ty.scope(func);
        let res_ty = func.map(|_, res| res.ty());
        let Some(res_ty) = res_ty.try_strengthen() else {
            panic!(
                "map_eq(): scope is dependently-typed.\n\
                res_ty: {:?}",
                res_ty,
            );
        };

        closed::congruence()
        .app(&val_name.to_term())
        .app(&arg_ty.to_term())
        .app(&res_ty.to_term())
        .app(&func.to_func(&val_name))
        .app(&val_0)
        .app(&val_1)
        .app(self)
    }

    fn map_eqs<const NUM_EQS: usize>(
        eqs: [&Tm<S>; NUM_EQS],
        func: impl FnOnce([Tm<S>; NUM_EQS]) -> Tm<S>,
    ) -> Tm<S> {
        let eqs = Ctx::into_common_ctx(eqs);
        let eq_tys = eqs.each_ref().map(|eq| {
            let (eq_term_0, _) = eq.ty().unwrap_equal();
            eq_term_0.ty()
        });
        let ctx = match eqs.first() {
            Some(eq) => eq.ctx(),
            None => {
                let dummy_empty = std::array::from_fn(|_| Ctx::root().unit_term());
                return func(dummy_empty).refl();
            },
        };

        let arg_names: [Name<S>; NUM_EQS] = std::array::from_fn(|index| {
            S::name_from_str(&format!("map_eqs_val_{}", index))
        });

        let (func, res_ty) = {
            let ctx_len = ctx.len();
            let mut ctx = ctx;
            for eq_ty in eq_tys.iter() {
                ctx = eq_ty.weaken_into(&ctx).cons()
            }
            let vars = std::array::from_fn(|index| {
                ctx.var(ctx_len + index)
            });

            let mut func = func(vars);
            let mut res_ty = func.ty();
            for (index, arg_name) in arg_names.iter().enumerate().rev() {
                func = Scope::new(func).to_func(&arg_name);
                res_ty = match Scope::new(res_ty).try_strengthen() {
                    Some(res_ty) => res_ty,
                    None => {
                        panic!("map_eqs: result type is dependent on argument {}", index);
                    },
                };
            }
            (func, res_ty)
        };

        let mut ret = closed::congruence_multi(NUM_EQS);
        for arg_name in arg_names {
            ret = ret.app(&arg_name.to_term());
        }
        for eq_ty in eq_tys.iter() {
            ret = ret.app(&eq_ty.to_term());
        }
        ret = ret.app(&res_ty.to_term());
        ret = ret.app(&func);
        for eq in eqs.iter() {
            let (eq_term_0, eq_term_1) = eq.ty().unwrap_equal();
            ret = ret.app(&eq_term_0).app(&eq_term_1).app(&eq);
        }

        ret
    }

    fn map_eq_dependent(
        &self,
        func: impl FnOnce(Tm<S>) -> Tm<S>,
    ) -> Tm<S> {
        let (eq_term_0, _) = self.ty().unwrap_equal();
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

    /*
    /// prove that self.map_eq(func_0).map_eq(func_1) == map_eq(|x| func_1(func_0(x)))
    fn map_eq_composition(
        &self,
        func_0: impl FnOnce(Tm<S>) -> Tm<S>,
        func_1: impl FnOnce(Tm<S>) -> Tm<S>,
    ) -> Tm<S> {
        let (eq_term_0, _) = self.ty().unwrap_equal();
        let eq_ty = eq_term_0.ty();
        let scope_0 = eq_ty.scope(func_0);
        let intermediate_ty = {
            scope_0
            .map(|_, term| term.ty())
            .try_strengthen()
            .expect("map_eq func_0 closure must not be dependently-typed")
        };
        let scope_1 = intermediate_ty.scope(func_1);

        self
        .cong(
            |_, _, val_eq| {
                val_eq
                .map_eq(scope_0.unbind())
                .map_eq(scope_1.unbind())
                .equals(&val_eq.map_eq(|val| scope_1.bind(&scope_0.bind(&val))))
            },
            |val| {
                scope_1.bind(&scope_0.bind(&val)).refl().refl()
            },
        )
    }
    */

    fn equality_contractible(&self, other: &Tm<S>) -> Tm<S> {
        let (val_eq_0, val_eq_1) = Ctx::into_common_ctx((self, other));
        let (val_0_0, val_1_0) = val_eq_0.ty().unwrap_equal();
        let (val_0_1, val_1_1) = val_eq_1.ty().unwrap_equal();
        let Some(val_0) = as_equal(&val_0_0, &val_0_1) else {
            panic!("\
                equality_contractible(): eq_term_0 differs between self and other.\n\
                self.eq_term_0: {:?}\n\
                other.eq_term_0: {:?}",
                val_0_0,
                val_0_1,
            );
        };
        let Some(val_1) = as_equal(&val_1_0, &val_1_1) else {
            panic!("\
                equality_contractible(): eq_term_1 differs between self and other.\n\
                self.eq_term_1: {:?}\n\
                other.eq_term_1: {:?}",
                val_1_0,
                val_1_1,
            );
        };

        closed::equality_contractible()
        .app(&val_0.ty().to_term())
        .app(&val_0)
        .app(&val_1)
        .app(&val_eq_0)
        .app(&val_eq_1)
    }

    fn equals_refl(&self) -> Tm<S> {
        let (eq_term_0, eq_term_1) = self.ty().unwrap_equal();
        let eq_term = as_equal(eq_term_0, eq_term_1).unwrap();

        closed::equals_refl()
        .app(&eq_term.ty().to_term())
        .app(&eq_term)
        .app(self)
    }

    fn try_find_alternate_term(&self) -> Option<(Tm<S>, Scope<S, Tm<S>>)> {
        match self.kind() {
            TmKind::Stuck { stuck } => {
                return stuck.try_find_alternate_term();
            },
            TmKind::Tag { tag } => {
                let mut s = S::try_tag_as_string(&tag)?;
                s.push_str("_alt");
                let alt_name = S::name_from_str(&s);
                let alt_term = alt_name.to_term();
                let scope = self.equals(&alt_term).scope(|eq| {
                    eq.tags_apart()
                });
                return Some((alt_term, scope));
            },
            TmKind::Type { ty } => {
                if let Some(uninhabited) = ty.try_prove_uninhabited() {
                    let inhabitant_name = S::name_from_str("unit");
                    let alt_term = self.ctx().unit_ty().to_term();
                    let scope = self.equals(&alt_term).scope(|eq| {
                        uninhabited
                        .contradiction(
                            &eq
                            .cong(
                                |ty_0, ty_1, _| {
                                    ty_1
                                    .to_ty()
                                    .pi(&inhabitant_name, |_| ty_0.to_ty())
                                },
                                |ty| ty.to_ty().func(&inhabitant_name, |x| x),
                            )
                            .app(&eq.ctx().unit_term())
                        )
                    });
                    return Some((alt_term, scope));
                }
                if let Some(term) = ty.try_find_arbitrary_term() {
                    let inhabitant_name = S::name_from_str("unit");
                    let alt_term = self.ctx().never().to_term();
                    let scope = self.equals(&alt_term).scope(|eq| {
                        eq
                        .cong(
                            |ty_0, ty_1, _| {
                                ty_0
                                .to_ty()
                                .pi(&inhabitant_name, |_| ty_1.to_ty())
                            },
                            |ty| ty.to_ty().func(&inhabitant_name, |x| x),
                        )
                        .app(&term)
                    });
                    return Some((alt_term, scope));
                }
            },
            TmKind::Zero => {
                let alt_term = self.ctx().nat_constant(1u32);
                let scope = self.equals(&alt_term).scope(|eq| {
                    eq.nat_eq()
                });
                return Some((alt_term, scope));
            },
            TmKind::Succs { .. } => {
                let alt_term = self.ctx().zero();
                let scope = self.equals(&alt_term).scope(|eq| {
                    eq.nat_eq()
                });
                return Some((alt_term, scope));
            },

            TmKind::Refl { .. } => (),
            TmKind::Unit => (),

            TmKind::InjLhs { lhs_name, lhs_term, rhs_ty } => {
                if let Some((lhs_alt_term, lhs_scope)) = lhs_term.try_find_alternate_term() {
                    let alt_term = lhs_alt_term.inj_lhs(&lhs_name, &rhs_ty);
                    let scope = self.equals(&alt_term).scope(|eq| {
                        lhs_scope.bind(&eq.case_eq())
                    });
                    return Some((alt_term, scope));
                }
                if let Some(rhs_term) = rhs_ty.try_find_arbitrary_term() {
                    let alt_term = rhs_term.inj_rhs(&lhs_name, &lhs_term.ty());
                    let scope = self.equals(&alt_term).scope(|eq| eq.case_eq());
                    return Some((alt_term, scope));
                }
            },

            TmKind::InjRhs { lhs_name, rhs_term, lhs_ty } => {
                if let Some((rhs_alt_term, rhs_scope)) = rhs_term.try_find_alternate_term() {
                    let alt_term = rhs_alt_term.inj_rhs(&lhs_name, &lhs_ty);
                    let scope = self.equals(&alt_term).scope(|eq| {
                        rhs_scope.bind(&eq.case_eq())
                    });
                    return Some((alt_term, scope));
                }
                if let Some(lhs_term) = lhs_ty.try_find_arbitrary_term() {
                    let alt_term = lhs_term.inj_lhs(&lhs_name, &rhs_term.ty());
                    let scope = self.equals(&alt_term).scope(|eq| eq.case_eq());
                    return Some((alt_term, scope));
                }
            },

            TmKind::Pair { head_name, tail_ty, head_term, tail_term } => {
                if let Some((tail_alt_term, tail_scope)) = tail_term.try_find_alternate_term() {
                    let alt_term = head_term.pair(
                        &head_name,
                        |head_term| tail_ty.bind(&head_term),
                        &tail_alt_term,
                    );
                    let scope = self.equals(&alt_term).scope(|eq| {
                        tail_scope
                        .bind(&eq.map_eq(|pair_term| pair_term.proj_tail()))
                    });
                    return Some((alt_term, scope));
                }
                if let Some((head_alt_term, head_scope)) = head_term.try_find_alternate_term() {
                    if let Some(tail_ty) = tail_ty.try_strengthen() {
                        let alt_term = head_alt_term.pair(&head_name, |_| tail_ty, &tail_term);
                        let scope = self.equals(&alt_term).scope(|eq| {
                            head_scope
                            .bind(&eq.map_eq(|pair_term| pair_term.proj_head()))
                        });
                        return Some((alt_term, scope));
                    }
                    if let Some(tail_alt_term) = tail_ty.bind(&head_alt_term).try_find_arbitrary_term() {
                        let alt_term = head_alt_term.pair(
                            &head_name,
                            |head_term| tail_ty.bind(&head_term),
                            &tail_alt_term,
                        );
                        let scope = self.equals(&alt_term).scope(|eq| {
                            head_scope
                            .bind(&eq.map_eq(|pair_term| pair_term.proj_head()))
                        });
                        return Some((alt_term, scope));
                    }
                }
            },

            TmKind::Func { arg_name, res_term } => {
                if let Some((res_alt_term, res_scope)) = res_term.map_out(|_, res_term| {
                    res_term.try_find_alternate_term()
                }) {
                    let res_alt_term = Scope::new(res_alt_term);
                    let res_scope = Scope::new(res_scope);

                    if let Some(arg_term) = res_term.var_ty().try_find_arbitrary_term() {
                        let alt_term = res_alt_term.to_func(&arg_name);
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
            TyKind::Stuck { .. } => None, // TODO
            TyKind::Name => {
                if let NameKind::Tag { tag: tag_0 } = self.to_name().kind()
                && let NameKind::Tag { tag: tag_1 } = other.to_name().kind()
                && tag_0 != tag_1
                {
                    todo!()
                }
                None
            },
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
                    TmKind::InjLhs { lhs_term: lhs_term_0, .. } => match other.kind() {
                        TmKind::Stuck { .. } => None,
                        TmKind::InjLhs { lhs_term: lhs_term_1, .. } => {
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
                    TmKind::InjRhs { rhs_term: rhs_term_0, .. } => match other.kind() {
                        TmKind::Stuck { .. } => None,
                        TmKind::InjLhs { .. } => {
                            Some(Uninhabited::new(
                                &self.equals(other),
                                |eq| eq.case_eq(),
                            ))
                        },
                        TmKind::InjRhs { rhs_term: rhs_term_1, .. } => {
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
            TyKind::Sigma { head_name: _, tail_ty } => {
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
            TyKind::Pi { arg_name: _, res_ty } => {
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

    fn type_equality_to_iso(&self) -> Iso<S> {
        let (eq_term_0, eq_term_1) = self.ty().unwrap_equal();
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

    fn apply_funext(&self, funext: &Tm<S>) -> Tm<S> {
        let (pointwise_eq, funext) = Ctx::into_common_ctx((self, funext));
        assert_eq!(funext.ty(), funext.ctx().function_extensionality_ty());

        let (arg_name, res_ty) = pointwise_eq.ty().unwrap_pi();
        let arg_ty = res_ty.var_ty();
        let (eq_term_0, eq_term_1) = res_ty.map_out(|_, res_ty| res_ty.unwrap_equal());
        let res_ty = Scope::new(eq_term_0.ty());
        let func_0 = Scope::new(eq_term_0).to_func(&arg_name);
        let func_1 = Scope::new(eq_term_1).to_func(&arg_name);

        funext
        .app(&arg_name.to_term())
        .app(&arg_ty.to_term())
        .app(&res_ty.map(|_, res_ty| res_ty.to_term()).to_func(&arg_name))
        .app(&func_0)
        .app(&func_1)
        .app(&pointwise_eq)
    }
}

