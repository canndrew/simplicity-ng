use crate::priv_prelude::*;

#[derive_where(Clone, Debug)]
#[derive(Contextual)]
#[scheme(S)]
pub struct Iso<S: Scheme> {
    fwd: Scope<S, Tm<S>>,
    rev: Scope<S, Tm<S>>,
    fwd_rev: Scope<S, Tm<S>>,
    rev_fwd: Scope<S, Tm<S>>,
}

impl<S: Scheme> Iso<S> {
    pub fn new(
        input_ty: &Ty<S>,
        output_ty: &Ty<S>,
        fwd: impl FnOnce(Tm<S>) -> Tm<S>,
        rev: impl FnOnce(Tm<S>) -> Tm<S>,
        fwd_rev: impl FnOnce(Tm<S>) -> Tm<S>,
        rev_fwd: impl FnOnce(Tm<S>) -> Tm<S>,
    ) -> Iso<S> {
        let fwd = input_ty.scope(fwd);
        let rev = output_ty.scope(rev);
        let fwd_rev = input_ty.scope(|term_0| {
            let ret = fwd_rev(term_0.clone());
            assert_eq!(
                ret.ty(),
                rev.bind(&fwd.bind(&term_0)).equals(&term_0),
            );
            ret
        });
        let rev_fwd = output_ty.scope(|term_1| {
            let ret = rev_fwd(term_1.clone());
            assert_eq!(
                ret.ty(),
                fwd.bind(&rev.bind(&term_1)).equals(&term_1),
            );
            ret
        });
        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    pub fn input_ty(&self) -> Ty<S> {
        self.fwd.var_ty()
    }

    pub fn output_ty(&self) -> Ty<S> {
        self.rev.var_ty()
    }

    pub fn fwd(&self, term_0: &Tm<S>) -> Tm<S> {
        self.fwd.bind(term_0)
    }

    pub fn rev(&self, term_1: &Tm<S>) -> Tm<S> {
        self.rev.bind(term_1)
    }

    pub fn fwd_rev(&self, term_0: &Tm<S>) -> Tm<S> {
        self.fwd_rev.bind(term_0)
    }

    pub fn rev_fwd(&self, term_1: &Tm<S>) -> Tm<S> {
        self.rev_fwd.bind(term_1)
    }

    pub fn symmetry(&self) -> Iso<S> {
        let Iso { fwd, rev, fwd_rev, rev_fwd } = self;
        Iso {
            fwd: rev.clone(),
            rev: fwd.clone(),
            fwd_rev: rev_fwd.clone(),
            rev_fwd: fwd_rev.clone(),
        }
    }

    pub fn transitivity(&self, other: &Iso<S>) -> Iso<S> {
        let fwd = self.fwd.map(|_, term_1| other.fwd.bind(&term_1));
        let rev = other.rev.map(|_, term_1| self.rev.bind(&term_1));
        let fwd_rev = self.fwd.var_ty().scope(|term_0| {
            self
            .rev
            .bind_eq(&other.fwd_rev.bind(&self.fwd.bind(&term_0)))
            .transitivity(&self.fwd_rev.bind(&term_0))
        });
        let rev_fwd = other.rev.var_ty().scope(|term_2| {
            other
            .fwd
            .bind_eq(&self.rev_fwd.bind(&other.rev.bind(&term_2)))
            .transitivity(&other.rev_fwd.bind(&term_2))
        });
        Iso { fwd, rev, fwd_rev, rev_fwd }
    }

    pub fn to_inj(&self) -> Inj<S> {
        let Iso { fwd, rev, fwd_rev, rev_fwd: _ } = self.clone();
        Inj::new(
            &fwd.var_ty(),
            |term| fwd.bind(&term),
            |term_0, term_1, fwd_eq| {
                fwd_rev
                .bind(&term_0)
                .symmetry()
                .transitivity(&rev.bind_eq(&fwd_eq))
                .transitivity(&fwd_rev.bind(&term_1))
            },
        )
    }

    pub fn to_epi(&self) -> Epi<S> {
        let Iso { fwd, rev, fwd_rev: _, rev_fwd } = self.clone();
        Epi { fwd, rev, rev_fwd }
    }

    pub fn is_definitionally_refl(&self) -> bool {
        (self.fwd.var_ty() == self.rev.var_ty()) &&
        self.fwd.map_out(|input, output| input == output) &&
        self.rev.map_out(|output, input| output == input)
    }

    pub fn sum_congruence(
        lhs_iso: &Iso<S>,
        rhs_iso: &Iso<S>,
    ) -> Iso<S> {
        let input_ty = Ty::sum(&lhs_iso.input_ty(), &rhs_iso.input_ty());
        let output_ty = Ty::sum(&lhs_iso.output_ty(), &rhs_iso.output_ty());
        Iso::new(
            &input_ty,
            &output_ty,
            |term| {
                term
                .case(
                    |_| output_ty.clone(),
                    |lhs_term| {
                        lhs_iso
                        .fwd
                        .bind(&lhs_term)
                        .inj_lhs(&rhs_iso.output_ty())
                    },
                    |rhs_term| {
                        rhs_iso
                        .fwd
                        .bind(&rhs_term)
                        .inj_rhs(&lhs_iso.output_ty())
                    },
                )
            },
            |term| {
                term
                .case(
                    |_| input_ty.clone(),
                    |lhs_term| {
                        lhs_iso
                        .rev
                        .bind(&lhs_term)
                        .inj_lhs(&rhs_iso.input_ty())
                    },
                    |rhs_term| {
                        rhs_iso
                        .rev
                        .bind(&rhs_term)
                        .inj_rhs(&lhs_iso.input_ty())
                    },
                )
            },

            |term| {
                term
                .case(
                    |term| {
                        term
                        .case(
                            |_| output_ty.clone(),
                            |lhs_term| {
                                lhs_iso
                                .fwd
                                .bind(&lhs_term)
                                .inj_lhs(&rhs_iso.output_ty())
                            },
                            |rhs_term| {
                                rhs_iso
                                .fwd
                                .bind(&rhs_term)
                                .inj_rhs(&lhs_iso.output_ty())
                            },
                        )
                        .case(
                            |_| input_ty.clone(),
                            |lhs_term| {
                                lhs_iso
                                .rev
                                .bind(&lhs_term)
                                .inj_lhs(&rhs_iso.input_ty())
                            },
                            |rhs_term| {
                                rhs_iso
                                .rev
                                .bind(&rhs_term)
                                .inj_rhs(&lhs_iso.input_ty())
                            },
                        )
                        .equals(&term)
                    },
                    |lhs_term| {
                        lhs_iso
                        .fwd_rev(&lhs_term)
                        .map_eq(|lhs_term| lhs_term.inj_lhs(&rhs_iso.input_ty()))
                    },
                    |rhs_term| {
                        rhs_iso
                        .fwd_rev(&rhs_term)
                        .map_eq(|rhs_term| rhs_term.inj_rhs(&lhs_iso.input_ty()))
                    },
                )
            },
            |term| {
                term
                .case(
                    |term| {
                        term
                        .case(
                            |_| input_ty.clone(),
                            |lhs_term| {
                                lhs_iso
                                .rev
                                .bind(&lhs_term)
                                .inj_lhs(&rhs_iso.input_ty())
                            },
                            |rhs_term| {
                                rhs_iso
                                .rev
                                .bind(&rhs_term)
                                .inj_rhs(&lhs_iso.input_ty())
                            },
                        )
                        .case(
                            |_| output_ty.clone(),
                            |lhs_term| {
                                lhs_iso
                                .fwd
                                .bind(&lhs_term)
                                .inj_lhs(&rhs_iso.output_ty())
                            },
                            |rhs_term| {
                                rhs_iso
                                .fwd
                                .bind(&rhs_term)
                                .inj_rhs(&lhs_iso.output_ty())
                            },
                        )
                        .equals(&term)
                    },
                    |lhs_term| {
                        lhs_iso
                        .rev_fwd(&lhs_term)
                        .map_eq(|lhs_term| lhs_term.inj_lhs(&rhs_iso.output_ty()))
                    },
                    |rhs_term| {
                        rhs_iso
                        .rev_fwd(&rhs_term)
                        .map_eq(|rhs_term| rhs_term.inj_rhs(&lhs_iso.output_ty()))
                    },
                )
            },
        )
    }

    pub fn sigma_head_congruence(
        head_iso: &Iso<S>,
        tail_ty: impl FnOnce(Tm<S>) -> Ty<S>,
    ) -> Iso<S> {
        let input_head_ty = head_iso.input_ty();
        let input_tail_ty = input_head_ty.scope(tail_ty);
        let input_ty = input_head_ty.sigma(input_tail_ty.unbind());

        let output_head_ty = head_iso.output_ty();
        let output_tail_ty = output_head_ty.scope(|head_term| {
            let head_term = head_iso.rev(&head_term);
            input_tail_ty.bind(&head_term)
        });
        let output_ty = output_head_ty.sigma(output_tail_ty.unbind());

        Iso::new(
            &input_ty,
            &output_ty,
            |term| {
                head_iso
                .fwd(&term.proj_head())
                .pair(
                    output_tail_ty.unbind(),
                    &input_tail_ty
                    .bind_eq(&head_iso.fwd_rev(&term.proj_head()))
                    .symmetry()
                    .transport(&term.proj_tail())
                )
            },
            |term| {
                head_iso
                .rev
                .bind(&term.proj_head())
                .pair(input_tail_ty.unbind(), &term.proj_tail())
            },
            |term| {
                head_iso
                .fwd_rev
                .bind(&term.proj_head())
                .cong(
                    |head_0, head_1, head_eq| {
                        input_tail_ty
                        .bind(&head_1)
                        .pi(|tail| {
                            head_0
                            .pair(
                                input_tail_ty.unbind(),
                                &input_tail_ty
                                .bind_eq(&head_eq)
                                .symmetry()
                                .transport(&tail)
                            )
                            .equals(&head_1.pair(input_tail_ty.unbind(), &tail))
                        })
                    },
                    |head| {
                        input_tail_ty
                        .bind(&head)
                        .func(|tail| {
                            head.pair(input_tail_ty.unbind(), &tail).refl()
                        })
                    },
                )
                .app(&term.proj_tail())
            },
            |term| {
                let output_head_term = term.proj_head();
                let input_head_term = head_iso.rev(&output_head_term);

                input_tail_ty
                .bind_eq(&head_iso.fwd_rev(&input_head_term))
                .equality_contractible(
                    &output_head_ty
                    .scope(output_tail_ty.unbind())
                    .bind_eq(&head_iso.rev_fwd(&output_head_term))
                )
                .map_eq(|eq| {
                    head_iso
                    .fwd
                    .bind(&input_head_term)
                    .pair(
                        output_tail_ty.unbind(),
                        &eq.symmetry().transport(&term.proj_tail()),
                    )
                })
                .transitivity(
                    &head_iso
                    .rev_fwd
                    .bind(&output_head_term)
                    .cong(
                        |head_0, head_1, head_eq| {
                            output_tail_ty
                            .bind(&head_1)
                            .pi(|tail| {
                                head_0
                                .pair(
                                    output_tail_ty.unbind(),
                                    &output_head_ty
                                    .scope(output_tail_ty.unbind())
                                    .bind_eq(&head_eq)
                                    .symmetry()
                                    .transport(&tail)
                                )
                                .equals(
                                    &head_1
                                    .pair(
                                        output_tail_ty.unbind(),
                                        &tail,
                                    ),
                                )
                            })
                        },
                        |head| {
                            output_tail_ty
                            .bind(&head)
                            .func(|tail| {
                                head
                                .pair(output_tail_ty.unbind(), &tail)
                                .refl()
                            })
                        },
                    )
                    .app(&term.proj_tail())
                )
            },
        )
    }

    /*
    pub fn pi_arg_congruence(
        arg_iso: &Iso<S>,
        res_ty: impl FnOnce(Tm<S>) -> Ty<S>,
    ) -> Iso<S> {
        let res_ty = arg_iso.input_ty().scope(res_ty);
        let input_ty = res_ty.to_pi();
        let output_ty = arg_iso.output_ty().pi(|arg| res_ty.bind(&arg_iso.rev(&arg)));

        Iso::new(
            &input_ty,
            &output_ty,
            |term| {
                arg_iso
                .output_ty()
                .weaken_into(&term.ctx())
                .func(|arg| {
                    term.app(&arg_iso.rev(&arg))
                })
            },
            |term| {
                arg_iso
                .input_ty()
                .weaken_into(&term.ctx())
                .func(|arg| {
                    res_ty
                    .weaken_into(&arg.ctx())
                    .bind_eq(&arg_iso.fwd_rev(&arg))
                    .transport(&term.app(&arg_iso.fwd(&arg)))
                })
            },
            |term| {
                arg_iso
                .input_ty()
                .weaken_into(&term.ctx())
                .func(|arg| {
                    arg_iso
                    .fwd_rev(&arg)
                    .cong(
                        |arg_0, arg_1, arg_eq| {
                            res_ty
                            .weaken_into(&arg_eq.ctx())
                            .bind_eq(&arg_eq)
                            .transport(&term.app(&arg_0))
                            .equals(&term.app(&arg_1))
                        },
                        |arg| term.app(&arg).refl(),
                    )
                })
                .funext()
            },
            |term| {
                arg_iso
                .output_ty()
                .weaken_into(&term.ctx())
                .func(|arg| {
                    res_ty
                    .bind(&arg_iso.rev(&arg_iso.fwd(&arg_iso.rev(&arg))))
                    .to_term()
                    .equals(&res_ty.bind(&arg_iso.rev(&arg)).to_term())
                    .scope(|eq| {
                        eq
                        .transport(&term.app(&arg_iso.fwd(&arg_iso.rev(&arg))))
                    })
                    .bind_eq(
                        &res_ty
                        .bind_eq(
                            &arg_iso
                            .fwd_rev(&arg_iso.rev(&arg))
                        )
                        .equality_contractible(
                            &arg_iso
                            .output_ty()
                            .scope(|arg| {
                                res_ty.bind(&arg_iso.rev(&arg)).to_term()
                            })
                            .bind_eq(&arg_iso.rev_fwd(&arg))
                        )
                    )
                    .transitivity(
                        &arg_iso
                        .rev_fwd(&arg)
                        .cong(
                            |arg_0, arg_1, arg_eq| {
                                arg_iso
                                .output_ty()
                                .scope(|arg| {
                                    res_ty.bind(&arg_iso.rev(&arg)).to_term()
                                })
                                .bind_eq(&arg_eq)
                                .transport(&term.app(&arg_0))
                                .equals(&term.app(&arg_1))
                            },
                            |arg| term.app(&arg).refl(),
                        )
                    )
                })
                .funext()
            },
        )
    }
    */

    pub fn sum_never_lhs_identity(rhs_ty: &Ty<S>) -> Iso<S> {
        Iso::new(
            &Ty::sum(&rhs_ty.ctx().never(), rhs_ty),
            rhs_ty,
            |term| term.case(
                |_| rhs_ty.clone(),
                |lhs_term| lhs_term.explode(|_| rhs_ty.clone()),
                |rhs_term| rhs_term,
            ),
            |term| term.inj_rhs(&term.ctx().never()),
            |term| term.case(
                |term| {
                    term
                    .case(
                        |_| rhs_ty.clone(),
                        |lhs_term| lhs_term.explode(|_| rhs_ty.clone()),
                        |rhs_term| rhs_term,
                    )
                    .inj_rhs(&term.ctx().never())
                    .equals(&term)
                },
                |lhs_term| {
                    lhs_term
                    .explode(
                        |lhs_term| {
                            lhs_term
                            .explode(|_| rhs_ty.clone())
                            .inj_rhs(&lhs_term.ctx().never())
                            .equals(&lhs_term.inj_lhs(rhs_ty))
                        },
                    )
                },
                |rhs_term| rhs_term.inj_rhs(&rhs_term.ctx().never()).refl(),
            ),
            |term| term.refl(),
        )
    }

    pub fn sum_never_rhs_identity(lhs_ty: &Ty<S>) -> Iso<S> {
        Iso::new(
            &Ty::sum(&lhs_ty.ctx().never(), lhs_ty),
            lhs_ty,
            |term| term.case(
                |_| lhs_ty.clone(),
                |lhs_term| lhs_term,
                |rhs_term| rhs_term.explode(|_| lhs_ty.clone()),
            ),
            |term| term.inj_lhs(&term.ctx().never()),
            |term| term.case(
                |term| {
                    term
                    .case(
                        |_| lhs_ty.clone(),
                        |lhs_term| lhs_term,
                        |rhs_term| rhs_term.explode(|_| lhs_ty.clone()),
                    )
                    .inj_lhs(&term.ctx().never())
                    .equals(&term)
                },
                |lhs_term| lhs_term.inj_lhs(&lhs_term.ctx().never()).refl(),
                |rhs_term| {
                    rhs_term
                    .explode(
                        |rhs_term| {
                            rhs_term
                            .explode(|_| lhs_ty.clone())
                            .inj_lhs(&rhs_term.ctx().never())
                            .equals(&rhs_term.inj_rhs(lhs_ty))
                        },
                    )
                },
            ),
            |term| term.refl(),
        )
    }

    pub fn sigma_unit_head_identity(
        ctx: &Ctx<S>,
        tail_ty: impl FnOnce(Tm<S>) -> Ty<S>,
    ) -> Iso<S> {
        let tail_ty = ctx.unit_ty().scope(tail_ty);
        let input_ty = ctx.unit_ty().sigma(tail_ty.unbind());
        Iso::new(
            &input_ty,
            &tail_ty.bind(&ctx.unit_term()),
            |term| term.proj_tail(),
            |term| ctx.unit_term().pair(
                |head_term| tail_ty.bind(&head_term),
                &term,
            ),
            |term| term.refl(),
            |term| term.refl(),
        )
    }

    pub fn sigma_unit_tail_identity(
        head_ty: &Ty<S>,
    ) -> Iso<S> {
        let input_ty = head_ty.sigma(|head_term| head_term.ctx().unit_ty());
        Iso::new(
            &input_ty,
            head_ty,
            |term| term.proj_head(),
            |term| term.pair(
                |head_term| head_term.ctx().unit_ty(),
                &term.ctx().unit_term(),
            ),
            |term| term.refl(),
            |term| term.refl(),
        )
    }

    pub fn sigma_never_head_annihilate(
        ctx: &Ctx<S>,
        tail_ty: impl FnOnce(Tm<S>) -> Ty<S>,
    ) -> Iso<S> {
        let input_ty = ctx.never().sigma(tail_ty);
        Iso::new(
            &input_ty,
            &ctx.never(),
            |term| term.proj_head(),
            |term| term.explode(|_| input_ty.clone()),
            |term| {
                term
                .proj_head()
                .explode(|term| {
                    term.proj_head().explode(|_| input_ty.clone()).equals(&term)
                })
            },
            |term| {
                term
                .explode(|term| {
                    term.explode(|_| input_ty.clone()).proj_head().equals(&term)
                })
            },
        )
    }

    pub fn sigma_never_tail_annihilate(
        head_ty: &Ty<S>,
    ) -> Iso<S> {
        let input_ty = head_ty.sigma(|head_term| head_term.ctx().never());
        Iso::new(
            &input_ty,
            &head_ty.ctx().never(),
            |term| term.proj_tail(),
            |term| term.explode(|_| input_ty.clone()),
            |term| {
                term
                .proj_tail()
                .explode(|term| {
                    term.proj_tail().explode(|_| input_ty.clone()).equals(&term)
                })
            },
            |term| {
                term
                .explode(|term| {
                    term.explode(|_| input_ty.clone()).proj_tail().equals(&term)
                })
            },
        )
    }

    pub fn sigma_equality_cancel(
        head_term: &Tm<S>,
    ) -> Iso<S> {
        let head_ty = head_term.ty();
        let tail_ty = head_ty.scope(|head_x| head_x.equals(&head_term));
        let input_ty = head_ty.sigma(tail_ty.unbind());
        Iso::new(
            &input_ty,
            &head_ty.ctx().unit_ty(),
            |term| term.ctx().unit_term(),
            |_term| head_term.pair(
                |term| term.equals(&head_term),
                &head_term.refl(),
            ),
            |term| {
                let head_eq = term.proj_tail().symmetry();
                let tail_eq = {
                    head_eq
                    .cong(
                        |head_0, head_1, head_eq| {
                            head_0
                            .equals(&head_term)
                            .pi(|tail_0| {
                                head_1
                                .weaken_into(&tail_0.ctx())
                                .equals(&head_term)
                                .pi(|tail_1| {
                                    tail_ty
                                    .weaken_into(&tail_1.ctx())
                                    .bind_eq(&head_eq.weaken_into(&tail_1.ctx()))
                                    .heterogeneous_equal(&tail_0.weaken_into(&tail_1.ctx()), &tail_1)
                                })
                            })
                        },
                        |head_x| {
                            head_x
                            .equals(&head_term)
                            .func(|tail_0| {
                                head_x
                                .weaken_into(&tail_0.ctx())
                                .equals(&head_term)
                                .func(|tail_1| {
                                    tail_0.equality_contractible(&tail_1)
                                })
                            })
                        },
                    )
                    .app(&head_term.refl())
                    .app(&term.proj_tail())
                };
                head_eq
                .pair_eq(
                    tail_ty.unbind(),
                    &head_term.refl(),
                    &term.proj_tail(),
                    &tail_eq
                )
            },
            |term| term.refl(),
        )
    }

    pub fn sigma_reassociate_to_head(
        head_ty: &Ty<S>,
        tail_head_ty: impl FnOnce(Tm<S>) -> Ty<S>,
        tail_tail_ty: impl FnOnce(Tm<S>, Tm<S>) -> Ty<S>,
    ) -> Iso<S> {
        let tail_head_ty = head_ty.scope(tail_head_ty);
        let tail_tail_ty = head_ty.scope(|head| {
            tail_head_ty.bind(&head).scope(|tail_head| tail_tail_ty(head, tail_head))
        });
        let input_ty = head_ty.sigma(|head| {
            tail_head_ty.bind(&head).sigma(|tail_head| {
                tail_tail_ty.bind(&head).bind(&tail_head)
            })
        });
        let output_ty = {
            head_ty
            .sigma(|head| tail_head_ty.bind(&head))
            .sigma(|pair| tail_tail_ty.bind(&pair.proj_head()).bind(&pair.proj_tail()))
        };
        Iso::new(
            &input_ty,
            &output_ty,
            |term| {
                let head = term.proj_head();
                let outer_tail = term.proj_tail();
                let tail_head = outer_tail.proj_head();
                let tail_tail = outer_tail.proj_tail();

                head
                .pair(
                    |head| tail_head_ty.bind(&head),
                    &tail_head,
                )
                .pair(
                    |pair| tail_tail_ty.bind(&pair.proj_head()).bind(&pair.proj_tail()),
                    &tail_tail,
                )
            },
            |term| {
                let outer_head = term.proj_head();
                let head = outer_head.proj_head();
                let tail_head = outer_head.proj_tail();
                let tail_tail = term.proj_tail();

                head
                .pair(
                    |head| {
                        tail_head_ty
                        .bind(&head)
                        .sigma(|tail_head| tail_tail_ty.bind(&head).bind(&tail_head))
                    },
                    &tail_head
                    .pair(
                        |tail_head| tail_tail_ty.bind(&head).bind(&tail_head),
                        &tail_tail,
                    )
                )
            },
            |term| term.refl(),
            |term| term.refl(),
        )
    }

    pub fn sigma_reassociate_to_tail(
        head_head_ty: &Ty<S>,
        head_tail_ty: impl FnOnce(Tm<S>) -> Ty<S>,
        tail_ty: impl FnOnce(Tm<S>) -> Ty<S>,
    ) -> Iso<S> {
        let head_tail_ty = head_head_ty.scope(head_tail_ty);
        let tail_ty = head_head_ty.sigma(head_tail_ty.unbind()).scope(tail_ty);

        let new_tail_ty = head_head_ty.scope(|head_head_term| {
            head_tail_ty.bind(&head_head_term).sigma(
                |head_tail_term| tail_ty.bind(
                    &head_head_term.pair(
                        head_tail_ty.unbind(),
                        &head_tail_term,
                    )
                ),
            )
        });

        let input_ty = head_head_ty.sigma(head_tail_ty.unbind()).sigma(tail_ty.unbind());
        let output_ty = head_head_ty.sigma(new_tail_ty.unbind());

        Iso::new(
            &input_ty,
            &output_ty,
            |term| {
                let head_term = term.proj_head();
                let head_head_term = head_term.proj_head();
                let head_tail_term = head_term.proj_tail();
                let tail_term = term.proj_tail();

                head_head_term
                .pair(
                    new_tail_ty.unbind(),
                    &head_tail_term.pair(
                        |head_tail_term| tail_ty.bind(
                            &head_head_term
                            .pair(head_tail_ty.unbind(), &head_tail_term)
                        ),
                        &tail_term,
                    ),
                )
            },
            |term| {
                let head_head_term = term.proj_head();
                let head_tail_term = term.proj_tail().proj_head();
                let tail_term = term.proj_tail().proj_tail();

                head_head_term
                .pair(head_tail_ty.unbind(), &head_tail_term)
                .pair(tail_ty.unbind(), &tail_term)
            },
            |term| term.refl(),
            |term| term.refl(),
        )
    }

    pub fn sigma_commute(
        head_ty: &Ty<S>,
        tail_ty: &Ty<S>,
    ) -> Iso<S> {
        let input_ty = head_ty.sigma(|_| tail_ty.clone());
        let output_ty = tail_ty.sigma(|_| head_ty.clone());

        Iso::new(
            &input_ty,
            &output_ty,
            |term| {
                term
                .proj_tail()
                .pair(|_| head_ty.clone(), &term.proj_head())
            },
            |term| {
                term
                .proj_tail()
                .pair(|_| tail_ty.clone(), &term.proj_head())
            },
            |term| term.refl(),
            |term| term.refl(),
        )
    }

    pub fn sigma_head_sum_distribute(
        head_lhs_ty: &Ty<S>,
        head_rhs_ty: &Ty<S>,
        tail_ty: impl FnOnce(Tm<S>) -> Ty<S>,
    ) -> Iso<S> {
        let head_ty = Ty::sum(head_lhs_ty, head_rhs_ty);
        let tail_ty = head_ty.scope(tail_ty);

        let input_ty = head_ty.sigma(tail_ty.unbind());
        let output_ty = Ty::sum(
            &head_lhs_ty.sigma(|head_lhs_term| {
                tail_ty.bind(&head_lhs_term.inj_lhs(head_rhs_ty))
            }),
            &head_rhs_ty.sigma(|head_rhs_term| {
                tail_ty.bind(&head_rhs_term.inj_rhs(head_lhs_ty))
            }),
        );

        Iso::new(
            &input_ty,
            &output_ty,
            |term| {
                term
                .proj_head()
                .case(
                    |_| output_ty.clone(),
                    |head_lhs_term| head_lhs_term.pair(
                        |head_lhs_term| tail_ty.bind(&head_lhs_term.inj_lhs(head_rhs_ty)),
                        &term.proj_tail(),
                    ),
                    |head_rhs_term| head_rhs_term.pair(
                        |head_rhs_term| tail_ty.bind(&head_rhs_term.inj_rhs(head_lhs_ty)),
                        &term.proj_tail(),
                    ),
                )
            },
            |term| {
                term
                .case(
                    |_| input_ty.clone(),
                    |lhs_term| {
                        lhs_term
                        .proj_head()
                        .inj_lhs(head_rhs_ty)
                        .pair(tail_ty.unbind(), &lhs_term.proj_tail())
                    },
                    |rhs_term| {
                        rhs_term
                        .proj_head()
                        .inj_rhs(head_lhs_ty)
                        .pair(tail_ty.unbind(), &rhs_term.proj_tail())
                    },
                )
            },
            |term| term.refl(),
            |term| term.refl(),
        )
    }

    pub fn simplify_iso_further(&self) -> Iso<S> {
        let next_iso = self.output_ty().simplify_iso();
        self.transitivity(&next_iso)
    }
}

#[extension(pub trait ScopeIsoExt)]
impl<S: Scheme> Scope<S, Iso<S>> {
    fn sigma_tail_congruence(&self) -> Iso<S> {
        let input_tail_ty = self.map(|_, iso| iso.input_ty());
        let output_tail_ty = self.map(|_, iso| iso.output_ty());
        let tail_fwd = self.map(|_, iso| iso.fwd.clone());
        let tail_rev = self.map(|_, iso| iso.rev.clone());
        let tail_fwd_rev = self.map(|_, iso| iso.fwd_rev.clone());
        let tail_rev_fwd = self.map(|_, iso| iso.rev_fwd.clone());

        let input_ty = input_tail_ty.to_sigma();
        let output_ty = output_tail_ty.to_sigma();

        Iso::new(
            &input_ty,
            &output_ty,
            |term| {
                term
                .proj_head()
                .pair(
                    |head| output_tail_ty.bind(&head),
                    &tail_fwd.bind(&term.proj_head()).bind(&term.proj_tail()),
                )
            },
            |term| {
                term
                .proj_head()
                .pair(
                    |head| input_tail_ty.bind(&head),
                    &tail_rev.bind(&term.proj_head()).bind(&term.proj_tail()),
                )
            },
            |term| {
                tail_fwd_rev
                .bind(&term.proj_head())
                .bind(&term.proj_tail())
                .map_eq(|tail| {
                    term
                    .proj_head()
                    .pair(|head| input_tail_ty.bind(&head), &tail)
                })
            },
            |term| {
                tail_rev_fwd
                .bind(&term.proj_head())
                .bind(&term.proj_tail())
                .map_eq(|tail| {
                    tail
                    .proj_head()
                    .pair(|head| output_tail_ty.bind(&head), &tail)
                })
            },
        )
    }
}

