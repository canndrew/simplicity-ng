use crate::priv_prelude::*;

#[derive_where(Clone, Debug, PartialEq)]
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
        same_ctx!(input_ty, output_ty);

        let fwd = input_ty.scope(fwd);
        let rev = output_ty.scope(rev);
        debug_assert_eq!(
            fwd.map(|_, output| output.ty()).try_strengthen().unwrap(),
            output_ty,
        );
        debug_assert_eq!(
            rev.map(|_, input| input.ty()).try_strengthen().unwrap(),
            input_ty,
        );
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
        let (iso_0, iso_1) = Ctx::into_common_ctx((self, other));
        let fwd = iso_0.fwd.map(|_, term_1| iso_1.fwd.bind(&term_1));
        let rev = iso_1.rev.map(|_, term_1| iso_0.rev.bind(&term_1));
        let fwd_rev = iso_0.fwd.var_ty().scope(|term_0| {
            iso_0
            .rev
            .bind_eq(&iso_1.fwd_rev.bind(&iso_0.fwd.bind(&term_0)))
            .transitivity(&iso_0.fwd_rev.bind(&term_0))
        });
        let rev_fwd = iso_1.rev.var_ty().scope(|term_2| {
            iso_1
            .fwd
            .bind_eq(&iso_0.rev_fwd.bind(&iso_1.rev.bind(&term_2)))
            .transitivity(&iso_1.rev_fwd.bind(&term_2))
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

    pub fn equality_equality_to_unit(
        eq_0: &Tm<S>,
        eq_1: &Tm<S>,
    ) -> Iso<S> {
        same_ctx!(eq_0, eq_1);
        let input_ty = eq_0.equals(&eq_1);
        let output_ty = eq_0.ctx().unit_ty();

        Iso::new(
            &input_ty,
            &output_ty,
            |eq_eq| eq_eq.ctx().unit_term(),
            |_| eq_0.equality_contractible(&eq_1),
            |eq_eq| {
                eq_0
                .equality_contractible(&eq_1)
                .equality_contractible(&eq_eq)
            },
            |unit| unit.refl(),
        )
    }

    pub fn sum_injective_lhs(
        lhs_name: &Name<S>,
        lhs_term_0: &Tm<S>,
        lhs_term_1: &Tm<S>,
        rhs_ty: &Ty<S>,
    ) -> Iso<S> {
        same_ctx!(lhs_name, lhs_term_0, lhs_term_1, rhs_ty);
        let input_ty = {
            lhs_term_0
            .inj_lhs(&lhs_name, &rhs_ty)
            .equals(&lhs_term_1.inj_lhs(&lhs_name, &rhs_ty))
        };
        let output_ty = lhs_term_0.equals(&lhs_term_1);

        Iso::new(
            &input_ty,
            &output_ty,
            |eq| eq.case_eq(),
            |eq| eq.map_eq(|lhs_term| lhs_term.inj_lhs(&lhs_name, &rhs_ty)),
            |eq| {
                eq
                .case_eq()
                .map_eq(|lhs_term| lhs_term.inj_lhs(&lhs_name, &rhs_ty))
                .equality_contractible(&eq)
            },
            |eq| {
                eq
                .map_eq(|lhs_term| lhs_term.inj_lhs(&lhs_name, &rhs_ty))
                .case_eq()
                .equality_contractible(&eq)
            },
        )
    }

    pub fn sum_injective_rhs(
        lhs_name: &Name<S>,
        rhs_term_0: &Tm<S>,
        rhs_term_1: &Tm<S>,
        lhs_ty: &Ty<S>,
    ) -> Iso<S> {
        same_ctx!(lhs_name, rhs_term_0, rhs_term_1, lhs_ty);
        let input_ty = {
            rhs_term_0
            .inj_rhs(&lhs_name, &lhs_ty)
            .equals(&rhs_term_1.inj_rhs(&lhs_name, &lhs_ty))
        };
        let output_ty = rhs_term_0.equals(&rhs_term_1);

        Iso::new(
            &input_ty,
            &output_ty,
            |eq| eq.case_eq(),
            |eq| eq.map_eq(|rhs_term| rhs_term.inj_rhs(&lhs_name, &lhs_ty)),
            |eq| {
                eq
                .case_eq()
                .map_eq(|rhs_term| rhs_term.inj_rhs(&lhs_name, &lhs_ty))
                .equality_contractible(&eq)
            },
            |eq| {
                eq
                .map_eq(|rhs_term| rhs_term.inj_rhs(&lhs_name, &lhs_ty))
                .case_eq()
                .equality_contractible(&eq)
            },
        )
    }

    pub fn sum_congruence(
        input_lhs_name: &Name<S>,
        output_lhs_name: &Name<S>,
        lhs_iso: &Iso<S>,
        rhs_iso: &Iso<S>,
    ) -> Iso<S> {
        same_ctx!(input_lhs_name, output_lhs_name, lhs_iso, rhs_iso);
        let input_ty = lhs_iso.input_ty().sum(&input_lhs_name, &rhs_iso.input_ty());
        let output_ty = lhs_iso.output_ty().sum(&output_lhs_name, &rhs_iso.output_ty());
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
                        .inj_lhs(&output_lhs_name, &rhs_iso.output_ty())
                    },
                    |rhs_term| {
                        rhs_iso
                        .fwd
                        .bind(&rhs_term)
                        .inj_rhs(&output_lhs_name, &lhs_iso.output_ty())
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
                        .inj_lhs(&input_lhs_name, &rhs_iso.input_ty())
                    },
                    |rhs_term| {
                        rhs_iso
                        .rev
                        .bind(&rhs_term)
                        .inj_rhs(&input_lhs_name, &lhs_iso.input_ty())
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
                                .inj_lhs(&output_lhs_name, &rhs_iso.output_ty())
                            },
                            |rhs_term| {
                                rhs_iso
                                .fwd
                                .bind(&rhs_term)
                                .inj_rhs(&output_lhs_name, &lhs_iso.output_ty())
                            },
                        )
                        .case(
                            |_| input_ty.clone(),
                            |lhs_term| {
                                lhs_iso
                                .rev
                                .bind(&lhs_term)
                                .inj_lhs(&input_lhs_name, &rhs_iso.input_ty())
                            },
                            |rhs_term| {
                                rhs_iso
                                .rev
                                .bind(&rhs_term)
                                .inj_rhs(&input_lhs_name, &lhs_iso.input_ty())
                            },
                        )
                        .equals(&term)
                    },
                    |lhs_term| {
                        lhs_iso
                        .fwd_rev(&lhs_term)
                        .map_eq(|lhs_term| lhs_term.inj_lhs(&input_lhs_name, &rhs_iso.input_ty()))
                    },
                    |rhs_term| {
                        rhs_iso
                        .fwd_rev(&rhs_term)
                        .map_eq(|rhs_term| rhs_term.inj_rhs(&input_lhs_name, &lhs_iso.input_ty()))
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
                                .inj_lhs(&input_lhs_name, &rhs_iso.input_ty())
                            },
                            |rhs_term| {
                                rhs_iso
                                .rev
                                .bind(&rhs_term)
                                .inj_rhs(&input_lhs_name, &lhs_iso.input_ty())
                            },
                        )
                        .case(
                            |_| output_ty.clone(),
                            |lhs_term| {
                                lhs_iso
                                .fwd
                                .bind(&lhs_term)
                                .inj_lhs(&output_lhs_name, &rhs_iso.output_ty())
                            },
                            |rhs_term| {
                                rhs_iso
                                .fwd
                                .bind(&rhs_term)
                                .inj_rhs(&output_lhs_name, &lhs_iso.output_ty())
                            },
                        )
                        .equals(&term)
                    },
                    |lhs_term| {
                        lhs_iso
                        .rev_fwd(&lhs_term)
                        .map_eq(|lhs_term| lhs_term.inj_lhs(&output_lhs_name, &rhs_iso.output_ty()))
                    },
                    |rhs_term| {
                        rhs_iso
                        .rev_fwd(&rhs_term)
                        .map_eq(|rhs_term| rhs_term.inj_rhs(&output_lhs_name, &lhs_iso.output_ty()))
                    },
                )
            },
        )
    }

    pub fn sigma_head_congruence(
        input_head_name: &Name<S>,
        output_head_name: &Name<S>,
        head_iso: &Iso<S>,
        tail_ty: impl FnOnce(Tm<S>) -> Ty<S>,
        tail_name: &Name<S>,
    ) -> Iso<S> {
        same_ctx!(input_head_name, output_head_name, head_iso, tail_name);

        let input_head_ty = head_iso.input_ty();
        let input_tail_ty = input_head_ty.scope(tail_ty);
        let input_ty = input_head_ty.sigma(&input_head_name, input_tail_ty.unbind());

        let output_head_ty = head_iso.output_ty();
        let output_tail_ty = output_head_ty.scope(|head_term| {
            let head_term = head_iso.rev(&head_term);
            input_tail_ty.bind(&head_term)
        });
        let output_ty = output_tail_ty.to_sigma(&output_head_name);

        Iso::new(
            &input_ty,
            &output_ty,
            |term| {
                head_iso
                .fwd(&term.proj_head())
                .pair(
                    &output_head_name,
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
                .pair(&input_head_name, input_tail_ty.unbind(), &term.proj_tail())
            },
            |term| {
                head_iso
                .fwd_rev
                .bind(&term.proj_head())
                .cong(
                    |head_0, head_1, head_eq| {
                        input_tail_ty
                        .bind(&head_1)
                        .pi(&tail_name, |tail| {
                            head_0
                            .pair(
                                &input_head_name,
                                input_tail_ty.unbind(),
                                &input_tail_ty
                                .bind_eq(&head_eq)
                                .symmetry()
                                .transport(&tail)
                            )
                            .equals(&head_1.pair(&input_head_name, input_tail_ty.unbind(), &tail))
                        })
                    },
                    |head| {
                        input_tail_ty
                        .bind(&head)
                        .func(&tail_name, |tail| {
                            head.pair(&input_head_name, input_tail_ty.unbind(), &tail).refl()
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
                        &output_head_name,
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
                            .pi(&tail_name, |tail| {
                                head_0
                                .pair(
                                    &output_head_name,
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
                                        &output_head_name,
                                        output_tail_ty.unbind(),
                                        &tail,
                                    ),
                                )
                            })
                        },
                        |head| {
                            output_tail_ty
                            .bind(&head)
                            .func(&tail_name, |tail| {
                                head
                                .pair(&output_head_name, output_tail_ty.unbind(), &tail)
                                .refl()
                            })
                        },
                    )
                    .app(&term.proj_tail())
                )
            },
        )
    }

    pub fn sigma_tail_congruence(
        head_name: &Name<S>,
        head_ty: &Ty<S>,
        tail_iso: impl FnOnce(Tm<S>) -> Iso<S>,
    ) -> Iso<S> {
        same_ctx!(head_name, head_ty);
        let tail_iso = head_ty.scope(tail_iso);
        let input_tail_ty = tail_iso.map(|_, tail_iso| tail_iso.input_ty());
        let output_tail_ty = tail_iso.map(|_, tail_iso| tail_iso.output_ty());
        let tail_fwd = tail_iso.map(|_, tail_iso| tail_iso.fwd.clone());
        let tail_rev = tail_iso.map(|_, tail_iso| tail_iso.rev.clone());
        let tail_fwd_rev = tail_iso.map(|_, tail_iso| tail_iso.fwd_rev.clone());
        let tail_rev_fwd = tail_iso.map(|_, tail_iso| tail_iso.rev_fwd.clone());

        let input_ty = input_tail_ty.to_sigma(&head_name);
        let output_ty = output_tail_ty.to_sigma(&head_name);

        Iso::new(
            &input_ty,
            &output_ty,
            |term| {
                term
                .proj_head()
                .pair(
                    &head_name,
                    |head| output_tail_ty.bind(&head),
                    &tail_fwd.bind(&term.proj_head()).bind(&term.proj_tail()),
                )
            },
            |term| {
                term
                .proj_head()
                .pair(
                    &head_name,
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
                    .pair(&head_name, |head| input_tail_ty.bind(&head), &tail)
                })
            },
            |term| {
                tail_rev_fwd
                .bind(&term.proj_head())
                .bind(&term.proj_tail())
                .map_eq(|tail| {
                    term
                    .proj_head()
                    .pair(&head_name, |head| output_tail_ty.bind(&head), &tail)
                })
            },
        )
    }

    pub fn sigma_equality_to_projected_field_equalities(
        head_name: &Name<S>,
        tail_ty: impl FnOnce(Tm<S>) -> Ty<S>,
        head_0: &Tm<S>,
        head_1: &Tm<S>,
        tail_0: &Tm<S>,
        tail_1: &Tm<S>,
    ) -> Iso<S> {
        same_ctx!(head_name, head_0, head_1, tail_0, tail_1);
        let tail_ty = head_0.ty().scope(tail_ty);
        let tail_0_name = S::name_from_str("tail_0");
        let tail_1_name = S::name_from_str("tail_1");
        let tail_eq_name = S::name_from_str("tail_eq");

        let input_ty = {
            head_0
            .pair(&head_name, tail_ty.unbind(), &tail_0)
            .equals(
                &head_1.pair(&head_name, tail_ty.unbind(), &tail_1),
            )
        };
        let output_ty = {
            head_0
            .equals(&head_1)
            .sigma(&head_name, |head_eq| {
                tail_ty
                .bind_eq(&head_eq)
                .heterogeneous_equal(&tail_0, &tail_1)
            })
        };

        let fwd = input_ty.scope(|pair_eq| {
            pair_eq
            .cong(
                |pair_0, pair_1, _| {
                    pair_0
                    .proj_head()
                    .equals(&pair_1.proj_head())
                    .sigma(
                        &head_name,
                        |head_eq| {
                            tail_ty
                            .bind_eq(&head_eq)
                            .heterogeneous_equal(
                                &pair_0.proj_tail(),
                                &pair_1.proj_tail(),
                            )
                        },
                    )
                },
                |pair| {
                    pair
                    .proj_head()
                    .refl()
                    .pair(
                        &head_name,
                        |head_eq| {
                            tail_ty
                            .bind_eq(&head_eq)
                            .heterogeneous_equal(
                                &pair.proj_tail(),
                                &pair.proj_tail(),
                            )
                        },
                        &pair.proj_tail().refl(),
                    )
                },
            )
        });

        let rev = output_ty.scope(|eq_pair| {
            eq_pair
            .proj_head()
            .cong(
                |head_0, head_1, head_eq| {
                    tail_ty
                    .bind(&head_0)
                    .pi(&tail_0_name, |tail_0| {
                        tail_ty
                        .bind(&head_1.weaken_into(&tail_0.ctx()))
                        .pi(&tail_1_name, |tail_1| {
                            tail_ty
                            .bind_eq(&head_eq.weaken_into(&tail_1.ctx()))
                            .heterogeneous_equal(&tail_0, &tail_1)
                            .pi(&tail_eq_name, |_| {
                                head_0
                                .pair(&head_name, tail_ty.unbind(), &tail_0)
                                .equals(&head_1.pair(&head_name, tail_ty.unbind(), &tail_1))
                            })
                        })
                    })
                },
                |head| {
                    tail_ty
                    .bind(&head)
                    .func(&tail_0_name, |tail_0| {
                        tail_ty
                        .bind(&head.weaken_into(&tail_0.ctx()))
                        .func(&tail_1_name, |tail_1| {
                            tail_0
                            .equals(&tail_1)
                            .func(&tail_eq_name, |tail_eq| {
                                tail_eq
                                .map_eq(|tail| head.pair(&head_name, tail_ty.unbind(), &tail))
                            })
                        })
                    })
                },
            )
            .app(&tail_0)
            .app(&tail_1)
            .app(&eq_pair.proj_tail())
        });

        let fwd_rev = input_ty.scope(|pair_eq| {
            rev
            .bind(&fwd.bind(&pair_eq))
            .equality_contractible(&pair_eq)
        });

        let rev_fwd = output_ty.scope(|eq_pair| {
            eq_pair
            .proj_head()
            .cong(
                |head_0, head_1, head_eq| {
                    tail_ty
                    .bind(&head_0)
                    .pi(&tail_0_name, |tail_0| {
                        tail_ty
                        .weaken_into(&tail_0.ctx())
                        .bind(&head_1)
                        .pi(&tail_1_name, |tail_1| {
                            tail_ty
                            .weaken_into(&tail_1.ctx())
                            .bind_eq(&head_eq)
                            .heterogeneous_equal(&tail_0, &tail_1)
                            .pi(&tail_eq_name, |tail_eq| {
                                head_eq
                                .weaken_into(&tail_eq.ctx())
                                .cong(
                                    |head_0, head_1, head_eq| {
                                        tail_ty
                                        .bind(&head_0)
                                        .pi(&tail_0_name, |tail_0| {
                                            tail_ty
                                            .weaken_into(&tail_0.ctx())
                                            .bind(&head_1)
                                            .pi(&tail_1_name, |tail_1| {
                                                tail_ty
                                                .weaken_into(&tail_1.ctx())
                                                .bind_eq(&head_eq)
                                                .heterogeneous_equal(&tail_0, &tail_1)
                                                .pi(&tail_eq_name, |_| {
                                                    head_0
                                                    .pair(&head_name, tail_ty.unbind(), &tail_0)
                                                    .equals(
                                                        &head_1
                                                        .pair(&head_name, tail_ty.unbind(), &tail_1),
                                                    )
                                                })
                                            })
                                        })
                                    },
                                    |head| {
                                        tail_ty
                                        .bind(&head)
                                        .func(&tail_0_name, |tail_0| {
                                            tail_ty
                                            .weaken_into(&tail_0.ctx())
                                            .bind(&head)
                                            .func(&tail_1_name, |tail_1| {
                                                tail_0
                                                .equals(&tail_1)
                                                .func(&tail_eq_name, |tail_eq| {
                                                    tail_eq
                                                    .map_eq(|tail| {
                                                        head
                                                        .pair(&head_name, tail_ty.unbind(), &tail)
                                                    })
                                                })
                                            })
                                        })
                                    },
                                )
                                .app(&tail_0)
                                .app(&tail_1)
                                .app(&tail_eq)
                                .cong(
                                    |pair_0, pair_1, _| {
                                        pair_0
                                        .proj_head()
                                        .equals(&pair_1.proj_head())
                                        .sigma(
                                            &head_name,
                                            |head_eq| {
                                                tail_ty
                                                .bind_eq(&head_eq)
                                                .heterogeneous_equal(
                                                    &pair_0.proj_tail(),
                                                    &pair_1.proj_tail(),
                                                )
                                            },
                                        )
                                    },
                                    |pair| {
                                        pair
                                        .proj_head()
                                        .refl()
                                        .pair(
                                            &head_name,
                                            |head_eq| {
                                                tail_ty
                                                .bind_eq(&head_eq)
                                                .heterogeneous_equal(
                                                    &pair.proj_tail(),
                                                    &pair.proj_tail(),
                                                )
                                            },
                                            &pair.proj_tail().refl(),
                                        )
                                    },
                                )
                                .equals(
                                    &head_eq
                                    .pair(
                                        &head_name,
                                        |head_eq| {
                                            tail_ty
                                            .bind_eq(&head_eq)
                                            .heterogeneous_equal(&tail_0, &tail_1)
                                        },
                                        &tail_eq,
                                    )
                                )
                            })
                        })
                    })
                },
                |head| {
                    tail_ty
                    .bind(&head)
                    .func(&tail_0_name, |tail_0| {
                        tail_ty
                        .weaken_into(&tail_0.ctx())
                        .bind(&head)
                        .func(&tail_1_name, |tail_1| {
                            tail_0
                            .equals(&tail_1)
                            .func(&tail_eq_name, |tail_eq| {
                                tail_eq
                                .cong(
                                    |tail_0, tail_1, tail_eq| {
                                        tail_eq
                                        .map_eq(|tail| {
                                            head.pair(&head_name, tail_ty.unbind(), &tail)
                                        })
                                        .cong(
                                            |pair_0, pair_1, _| {
                                                pair_0
                                                .proj_head()
                                                .equals(&pair_1.proj_head())
                                                .sigma(
                                                    &head_name,
                                                    |head_eq| {
                                                        tail_ty
                                                        .bind_eq(&head_eq)
                                                        .heterogeneous_equal(
                                                            &pair_0.proj_tail(),
                                                            &pair_1.proj_tail(),
                                                        )
                                                    },
                                                )
                                            },
                                            |pair| {
                                                pair
                                                .proj_head()
                                                .refl()
                                                .pair(
                                                    &head_name,
                                                    |head_eq| {
                                                        tail_ty
                                                        .bind_eq(&head_eq)
                                                        .heterogeneous_equal(
                                                            &pair.proj_tail(),
                                                            &pair.proj_tail(),
                                                        )
                                                    },
                                                    &pair.proj_tail().refl(),
                                                )
                                            },
                                        )
                                        .equals(
                                            &head
                                            .refl()
                                            .pair(
                                                &head_name,
                                                |head_eq| {
                                                    tail_ty
                                                    .bind_eq(&head_eq)
                                                    .heterogeneous_equal(&tail_0, &tail_1)
                                                },
                                                &tail_eq,
                                            )
                                        )
                                    },
                                    |tail| {
                                        head
                                        .refl()
                                        .pair(
                                            &head_name,
                                            |head_eq| {
                                                tail_ty
                                                .bind_eq(&head_eq)
                                                .heterogeneous_equal(&tail, &tail)
                                            },
                                            &tail.refl(),
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
            .app(&eq_pair.proj_tail())
        });

        Iso::new(
            &input_ty,
            &output_ty,
            fwd.unbind(),
            rev.unbind(),
            fwd_rev.unbind(),
            rev_fwd.unbind(),
        )
    }

    pub fn pi_arg_congruence(
        input_arg_name: &Name<S>,
        output_arg_name: &Name<S>,
        arg_iso: &Iso<S>,
        res_ty: impl FnOnce(Tm<S>) -> Ty<S>,
        funext: &Tm<S>,
    ) -> Iso<S> {
        same_ctx!(input_arg_name, output_arg_name, arg_iso, funext);
        let arg_ty_0 = arg_iso.input_ty();
        let arg_ty_1 = arg_iso.output_ty();
        let res_ty = arg_ty_0.scope(res_ty);

        assert_eq!(funext.ty(), funext.ctx().function_extensionality_ty());

        Iso::new(
            &res_ty.to_pi(&input_arg_name),
            &arg_ty_1.pi(&output_arg_name, |arg_1| res_ty.bind(&arg_iso.rev(&arg_1))),
            |func_0| {
                arg_ty_1
                .weaken_into(&func_0.ctx())
                .func(&output_arg_name, |arg_1| {
                    func_0.app(&arg_iso.rev(&arg_1))
                })
            },
            |func_1| {
                arg_ty_0
                .weaken_into(&func_1.ctx())
                .func(&input_arg_name, |arg_0| {
                    res_ty
                    .weaken_into(&arg_0.ctx())
                    .bind_eq(&arg_iso.fwd_rev(&arg_0))
                    .transport(
                        &func_1.app(&arg_iso.fwd(&arg_0))
                    )
                })
            },
            |func_0| {
                arg_ty_0
                .weaken_into(&func_0.ctx())
                .func(&input_arg_name, |arg_0| {
                    arg_iso
                    .fwd_rev(&arg_0)
                    .cong(
                        |arg_0_fwd_rev, arg_0, arg_0_eq| {
                            res_ty
                            .weaken_into(&arg_0_eq.ctx())
                            .bind_eq(&arg_0_eq)
                            .transport(
                                &func_0.app(&arg_0_fwd_rev)
                            )
                            .equals(
                                &func_0.app(&arg_0)
                            )
                        },
                        |arg_0| func_0.app(&arg_0).refl(),
                    )
                })
                .apply_funext(&funext)
            },
            |func_1| {
                arg_ty_1
                .weaken_into(&func_1.ctx())
                .func(&output_arg_name, |arg_1| {
                    arg_iso
                    .fwd_rev(&arg_iso.rev(&arg_1))
                    .equality_contractible(
                        &arg_iso
                        .rev_fwd(&arg_1)
                        .map_eq(|arg_1| arg_iso.rev(&arg_1))
                    )
                    .map_eq(|arg_eq| {
                        res_ty
                        .weaken_into(&arg_eq.ctx())
                        .bind_eq(&arg_eq)
                        .transport(
                            &func_1
                            .app(&arg_iso.fwd(&arg_iso.rev(&arg_1)))
                        )
                    })
                    .transitivity(
                        &arg_iso
                        .rev_fwd(&arg_1)
                        .cong(
                            |arg_1_rev_fwd, arg_1, arg_1_eq| {
                                res_ty
                                .weaken_into(&arg_1_eq.ctx())
                                .bind_eq(
                                    &arg_1_eq
                                    .map_eq(|arg_1| arg_iso.rev(&arg_1))
                                )
                                .transport(
                                    &func_1.app(&arg_1_rev_fwd)
                                )
                                .equals(
                                    &func_1.app(&arg_1)
                                )
                            },
                            |arg_1| {
                                func_1.app(&arg_1).refl()
                            },
                        )
                    )
                })
                .apply_funext(&funext)
            },
        )
    }

    pub fn pi_res_congruence(
        arg_name: &Name<S>,
        arg_ty: &Ty<S>,
        res_iso: impl FnOnce(Tm<S>) -> Iso<S>,
        funext: &Tm<S>,
    ) -> Iso<S> {
        same_ctx!(arg_name, arg_ty, funext);
        let res_iso = arg_ty.scope(res_iso);

        let arg_ty = res_iso.var_ty();
        let res_ty_0 = res_iso.map(|_, res_iso| res_iso.input_ty());
        let res_ty_1 = res_iso.map(|_, res_iso| res_iso.output_ty());

        Iso::new(
            &res_ty_0.to_pi(&arg_name),
            &res_ty_1.to_pi(&arg_name),
            |func_0| {
                arg_ty
                .weaken_into(&func_0.ctx())
                .func(&arg_name, |arg| {
                    res_iso
                    .bind(&arg)
                    .fwd(&func_0.app(&arg))
                })
            },
            |func_1| {
                arg_ty
                .weaken_into(&func_1.ctx())
                .func(&arg_name, |arg| {
                    res_iso
                    .bind(&arg)
                    .rev(&func_1.app(&arg))
                })
            },
            |func_0| {
                arg_ty
                .weaken_into(&func_0.ctx())
                .func(&arg_name, |arg| {
                    res_iso
                    .bind(&arg)
                    .fwd_rev(&func_0.app(&arg))
                })
                .apply_funext(&funext)
            },
            |func_1| {
                arg_ty
                .weaken_into(&func_1.ctx())
                .func(&arg_name, |arg| {
                    res_iso
                    .bind(&arg)
                    .rev_fwd(&func_1.app(&arg))
                })
                .apply_funext(&funext)
            },
        )

    }

    pub fn sum_never_lhs(
        lhs_name: &Name<S>,
        rhs_ty: &Ty<S>,
    ) -> Iso<S> {
        same_ctx!(lhs_name, rhs_ty);
        let input_ty = rhs_ty.ctx().never().sum(&lhs_name, &rhs_ty);
        Iso::new(
            &input_ty,
            &rhs_ty,
            |term| term.case(
                |_| rhs_ty.clone(),
                |lhs_term| lhs_term.explode(|_| rhs_ty.clone()),
                |rhs_term| rhs_term,
            ),
            |term| term.inj_rhs(&lhs_name, &term.ctx().never()),
            |term| term.case(
                |term| {
                    term
                    .case(
                        |_| rhs_ty.clone(),
                        |lhs_term| lhs_term.explode(|_| rhs_ty.clone()),
                        |rhs_term| rhs_term,
                    )
                    .inj_rhs(&lhs_name, &term.ctx().never())
                    .equals(&term)
                },
                |lhs_term| {
                    lhs_term
                    .explode(
                        |lhs_term| {
                            lhs_term
                            .explode(|_| rhs_ty.clone())
                            .inj_rhs(&lhs_name, &lhs_term.ctx().never())
                            .equals(&lhs_term.inj_lhs(&lhs_name, &rhs_ty))
                        },
                    )
                },
                |rhs_term| rhs_term.inj_rhs(&lhs_name, &rhs_term.ctx().never()).refl(),
            ),
            |term| term.refl(),
        )
    }

    pub fn sum_never_rhs(
        lhs_name: &Name<S>,
        lhs_ty: &Ty<S>,
    ) -> Iso<S> {
        same_ctx!(lhs_name, lhs_ty);
        let input_ty = lhs_ty.sum(&lhs_name, &lhs_ty.ctx().never());
        Iso::new(
            &input_ty,
            &lhs_ty,
            |term| term.case(
                |_| lhs_ty.clone(),
                |lhs_term| lhs_term,
                |rhs_term| rhs_term.explode(|_| lhs_ty.clone()),
            ),
            |term| term.inj_lhs(&lhs_name, &term.ctx().never()),
            |term| term.case(
                |term| {
                    term
                    .case(
                        |_| lhs_ty.clone(),
                        |lhs_term| lhs_term,
                        |rhs_term| rhs_term.explode(|_| lhs_ty.clone()),
                    )
                    .inj_lhs(&lhs_name, &term.ctx().never())
                    .equals(&term)
                },
                |lhs_term| lhs_term.inj_lhs(&lhs_name, &lhs_term.ctx().never()).refl(),
                |rhs_term| {
                    rhs_term
                    .explode(
                        |rhs_term| {
                            rhs_term
                            .explode(|_| lhs_ty.clone())
                            .inj_lhs(&lhs_name, &rhs_term.ctx().never())
                            .equals(&rhs_term.inj_rhs(&lhs_name, &lhs_ty))
                        },
                    )
                },
            ),
            |term| term.refl(),
        )
    }

    pub fn sigma_unit_head(
        head_name: &Name<S>,
        tail_ty: impl FnOnce(Tm<S>) -> Ty<S>,
    ) -> Iso<S> {
        let tail_ty = head_name.ctx().unit_ty().scope(tail_ty);
        let input_ty = head_name.ctx().unit_ty().sigma(&head_name, tail_ty.unbind());
        Iso::new(
            &input_ty,
            &tail_ty.bind(&head_name.ctx().unit_term()),
            |term| term.proj_tail(),
            |term| term.ctx().unit_term().pair(
                head_name,
                |head_term| tail_ty.bind(&head_term),
                &term,
            ),
            |term| term.refl(),
            |term| term.refl(),
        )
    }

    pub fn sigma_unit_tail(
        head_name: &Name<S>,
        head_ty: &Ty<S>,
    ) -> Iso<S> {
        same_ctx!(head_name, head_ty);
        let input_ty = head_ty.sigma(&head_name, |head_term| head_term.ctx().unit_ty());
        Iso::new(
            &input_ty,
            &head_ty,
            |term| term.proj_head(),
            |term| term.pair(
                &head_name,
                |head_term| head_term.ctx().unit_ty(),
                &term.ctx().unit_term(),
            ),
            |term| term.refl(),
            |term| term.refl(),
        )
    }

    pub fn sigma_never_head(
        head_name: &Name<S>,
        tail_ty: impl FnOnce(Tm<S>) -> Ty<S>,
    ) -> Iso<S> {
        let input_ty = head_name.ctx().never().sigma(&head_name, tail_ty);
        Iso::new(
            &input_ty,
            &head_name.ctx().never(),
            |term| term.proj_head(),
            |term| term.explode(|_| input_ty.clone()),
            |term| {
                term
                .proj_head()
                .explode(|_| {
                    term.proj_head().explode(|_| input_ty.clone()).equals(&term)
                })
            },
            |term| {
                term
                .explode(|_| {
                    term.explode(|_| input_ty.clone()).proj_head().equals(&term)
                })
            },
        )
    }

    pub fn sigma_never_tail(
        head_name: &Name<S>,
        head_ty: &Ty<S>,
    ) -> Iso<S> {
        same_ctx!(head_name, head_ty);
        let input_ty = head_ty.sigma(&head_name, |head_term| head_term.ctx().never());
        Iso::new(
            &input_ty,
            &head_ty.ctx().never(),
            |term| term.proj_tail(),
            |term| term.explode(|_| input_ty.clone()),
            |term| {
                term
                .proj_tail()
                .explode(|_| {
                    term.proj_tail().explode(|_| input_ty.clone()).equals(&term)
                })
            },
            |term| {
                term
                .explode(|_| {
                    term.explode(|_| input_ty.clone()).proj_tail().equals(&term)
                })
            },
        )
    }

    pub fn sigma_equality_cancel(
        head_name: &Name<S>,
        head_term: &Tm<S>,
    ) -> Iso<S> {
        same_ctx!(head_name, head_term);
        let head_ty = head_term.ty();
        let tail_ty = head_ty.scope(|head_x| head_x.equals(&head_term));
        let input_ty = head_ty.sigma(&head_name, tail_ty.unbind());

        let equality_0_name = S::name_from_str("equality_0");
        let equality_1_name = S::name_from_str("equality_1");

        Iso::new(
            &input_ty,
            &head_ty.ctx().unit_ty(),
            |term| term.ctx().unit_term(),
            |_term| head_term.pair(
                &head_name,
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
                            .pi(&equality_0_name, |tail_0| {
                                head_1
                                .weaken_into(&tail_0.ctx())
                                .equals(&head_term)
                                .pi(&equality_1_name, |tail_1| {
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
                            .func(&equality_0_name, |tail_0| {
                                head_x
                                .weaken_into(&tail_0.ctx())
                                .equals(&head_term)
                                .func(&equality_1_name, |tail_1| {
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
                    &head_name,
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
        head_name: &Name<S>,
        tail_head_name: &Name<S>,
        head_ty: &Ty<S>,
        tail_head_ty: impl FnOnce(Tm<S>) -> Ty<S>,
        tail_tail_ty: impl FnOnce(Tm<S>, Tm<S>) -> Ty<S>,
    ) -> Iso<S> {
        same_ctx!(head_name, head_ty, tail_head_name);

        let tail_head_ty = head_ty.scope(tail_head_ty);
        let tail_tail_ty = head_ty.scope(|head| {
            tail_head_ty.bind(&head).scope(|tail_head| tail_tail_ty(head, tail_head))
        });
        let input_ty = head_ty.sigma(&head_name, |head| {
            tail_head_ty.bind(&head).sigma(&tail_head_name, |tail_head| {
                tail_tail_ty.bind(&head).bind(&tail_head)
            })
        });
        let output_ty = {
            head_ty
            .sigma(&head_name, |head| tail_head_ty.bind(&head))
            .sigma(&tail_head_name, |pair| tail_tail_ty.bind(&pair.proj_head()).bind(&pair.proj_tail()))
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
                    &head_name,
                    |head| tail_head_ty.bind(&head),
                    &tail_head,
                )
                .pair(
                    &tail_head_name,
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
                    &head_name,
                    |head| {
                        tail_head_ty
                        .bind(&head)
                        .sigma(
                            &tail_head_name,
                            |tail_head| tail_tail_ty.bind(&head).bind(&tail_head),
                        )
                    },
                    &tail_head
                    .pair(
                        &tail_head_name,
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
        head_name: &Name<S>,
        head_head_name: &Name<S>,
        head_head_ty: &Ty<S>,
        head_tail_ty: impl FnOnce(Tm<S>) -> Ty<S>,
        tail_ty: impl FnOnce(Tm<S>) -> Ty<S>,
    ) -> Iso<S> {
        same_ctx!(head_name, head_head_name, head_head_ty);
        let head_tail_ty = head_head_ty.scope(head_tail_ty);
        let tail_ty = head_head_ty.sigma(&head_head_name, head_tail_ty.unbind()).scope(tail_ty);

        let new_tail_ty = head_head_ty.scope(|head_head_term| {
            head_tail_ty.bind(&head_head_term).sigma(
                &head_name,
                |head_tail_term| tail_ty.bind(
                    &head_head_term.pair(
                        &head_head_name,
                        head_tail_ty.unbind(),
                        &head_tail_term,
                    )
                ),
            )
        });

        let input_ty = {
            head_head_ty
            .sigma(&head_head_name, head_tail_ty.unbind())
            .sigma(&head_name, tail_ty.unbind())
        };
        let output_ty = {
            head_head_ty
            .sigma(&head_head_name, new_tail_ty.unbind())
        };

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
                    &head_head_name,
                    new_tail_ty.unbind(),
                    &head_tail_term.pair(
                        &head_name,
                        |head_tail_term| tail_ty.bind(
                            &head_head_term
                            .pair(&head_head_name, head_tail_ty.unbind(), &head_tail_term)
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
                .pair(&head_head_name, head_tail_ty.unbind(), &head_tail_term)
                .pair(&head_name, tail_ty.unbind(), &tail_term)
            },
            |term| term.refl(),
            |term| term.refl(),
        )
    }

    pub fn sigma_commute(
        head_name: &Name<S>,
        tail_name: &Name<S>,
        head_ty: &Ty<S>,
        tail_ty: &Ty<S>,
    ) -> Iso<S> {
        same_ctx!(head_name, tail_name, head_ty, tail_ty);

        let input_ty = head_ty.sigma(&head_name, |_| tail_ty.clone());
        let output_ty = tail_ty.sigma(&tail_name, |_| head_ty.clone());

        Iso::new(
            &input_ty,
            &output_ty,
            |term| {
                term
                .proj_tail()
                .pair(&tail_name, |_| head_ty.clone(), &term.proj_head())
            },
            |term| {
                term
                .proj_tail()
                .pair(&head_name, |_| tail_ty.clone(), &term.proj_head())
            },
            |term| term.refl(),
            |term| term.refl(),
        )
    }

    pub fn sigma_sum_head_distribute(
        head_name: &Name<S>,
        lhs_name: &Name<S>,
        head_lhs_ty: &Ty<S>,
        head_rhs_ty: &Ty<S>,
        tail_ty: impl FnOnce(Tm<S>) -> Ty<S>,
    ) -> Iso<S> {
        same_ctx!(head_name, lhs_name, head_lhs_ty, head_rhs_ty);
        let head_ty = head_lhs_ty.sum(&lhs_name, &head_rhs_ty);
        let tail_ty = head_ty.scope(tail_ty);
        let input_ty = head_ty.sigma(&head_name, tail_ty.unbind());

        let output_lhs_ty = head_lhs_ty.sigma(&head_name, |head_lhs| {
            tail_ty.bind(&head_lhs.inj_lhs(&lhs_name, &head_rhs_ty))
        });
        let output_rhs_ty = head_rhs_ty.sigma(&head_name, |head_rhs| {
            tail_ty.bind(&head_rhs.inj_rhs(&lhs_name, &head_lhs_ty))
        });
        let output_ty = output_lhs_ty.sum(&lhs_name, &output_rhs_ty);

        Iso::new(
            &input_ty,
            &output_ty,
            |term| {
                term
                .proj_head()
                .case(
                    |_| output_ty.clone(),
                    |head_lhs_term| head_lhs_term.pair(
                        &head_name,
                        |head_lhs_term| {
                            tail_ty
                            .bind(&head_lhs_term.inj_lhs(&lhs_name, &head_rhs_ty))
                        },
                        &term.proj_tail(),
                    ),
                    |head_rhs_term| head_rhs_term.pair(
                        &head_name,
                        |head_rhs_term| {
                            tail_ty
                            .bind(&head_rhs_term.inj_rhs(&lhs_name, &head_lhs_ty))
                        },
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
                        .inj_lhs(&lhs_name, &head_rhs_ty)
                        .pair(&head_name, tail_ty.unbind(), &lhs_term.proj_tail())
                    },
                    |rhs_term| {
                        rhs_term
                        .proj_head()
                        .inj_rhs(&lhs_name, &head_lhs_ty)
                        .pair(&head_name, tail_ty.unbind(), &rhs_term.proj_tail())
                    },
                )
            },
            |term| term.refl(),
            |term| term.refl(),
        )
    }

    pub fn pi_sigma_arg(
        arg_name: &Name<S>,
        head_name: &Name<S>,
        arg_head_ty: &Ty<S>,
        arg_tail_ty: impl FnOnce(Tm<S>) -> Ty<S>,
        res_ty: impl FnOnce(Tm<S>) -> Ty<S>,
    ) -> Iso<S> {
        same_ctx!(arg_name, head_name, arg_head_ty);
        let arg_tail_ty = arg_head_ty.scope(arg_tail_ty);
        let arg_ty = arg_tail_ty.to_sigma(&head_name);
        let res_ty = arg_ty.scope(res_ty);

        let input_ty = res_ty.to_pi(&arg_name);
        let output_ty = {
            arg_head_ty
            .pi(&head_name, |head| {
                arg_tail_ty
                .bind(&head)
                .pi(&arg_name, |tail| {
                    res_ty
                    .bind(&head.pair(&head_name, arg_tail_ty.unbind(), &tail))
                })
            })
        };

        let fwd = input_ty.scope(|input| {
            arg_head_ty
            .weaken_into(&input.ctx())
            .func(&head_name, |head| {
                arg_tail_ty
                .bind(&head)
                .func(&arg_name, |tail| {
                    input
                    .app(&head.pair(&head_name, arg_tail_ty.unbind(), &tail))
                })
            })
        });
        let rev = output_ty.scope(|output| {
            arg_ty
            .weaken_into(&output.ctx())
            .func(&arg_name, |pair| {
                output
                .app(&pair.proj_head())
                .app(&pair.proj_tail())
            })
        });
        let fwd_rev = input_ty.scope(|input| {
            input.refl()
        });
        let rev_fwd = output_ty.scope(|output| {
            output.refl()
        });
        Iso::new(
            &input_ty,
            &output_ty,
            fwd.unbind(),
            rev.unbind(),
            fwd_rev.unbind(),
            rev_fwd.unbind(),
        )
    }

    pub fn pi_never_arg(
        arg_name: &Name<S>,
        res_ty: impl FnOnce(Tm<S>) -> Ty<S>,
        funext: &Tm<S>,
    ) -> Iso<S> {
        same_ctx!(arg_name, funext);
        let res_ty = arg_name.ctx().never().scope(res_ty);
        let input_ty = res_ty.to_pi(&arg_name);
        let output_ty = arg_name.ctx().unit_ty();

        Iso::new(
            &input_ty,
            &output_ty,
            |func| func.ctx().unit_term(),
            |unit| {
                unit
                .ctx()
                .never()
                .func(&arg_name, |never| {
                    never.explode(|_| res_ty.bind(&never))
                })
            },
            |func| {
                func
                .ctx()
                .never()
                .func(&arg_name, |never| {
                    never
                    .explode(|_| {
                        never
                        .explode(|_| res_ty.bind(&never))
                        .equals(&func.app(&never))
                    })
                })
                .apply_funext(&funext)
            },
            |unit| unit.refl(),
        )
    }

    pub fn pi_unit_arg(
        arg_name: &Name<S>,
        res_ty: impl FnOnce(Tm<S>) -> Ty<S>,
    ) -> Iso<S> {
        let res_ty = arg_name.ctx().unit_ty().scope(res_ty);
        let input_ty = res_ty.to_pi(arg_name);
        let output_ty = res_ty.bind(&arg_name.ctx().unit_term());

        Iso::new(
            &input_ty,
            &output_ty,
            |func| func.app(&func.ctx().unit_term()),
            |res_term| {
                res_term
                .ctx()
                .unit_ty()
                .func(arg_name, |_| res_term)
            },
            |func| func.refl(),
            |res_term| res_term.refl(),
        )
    }

    pub fn pi_unit_res(
        arg_name: &Name<S>,
        arg_ty: &Ty<S>,
    ) -> Iso<S> {
        same_ctx!(arg_name, arg_ty);
        let input_ty = arg_ty.pi(&arg_name, |arg| arg.ctx().unit_ty());
        let output_ty = arg_ty.ctx().unit_ty();

        Iso::new(
            &input_ty,
            &output_ty,
            |func| func.ctx().unit_term(),
            |_| arg_ty.func(&arg_name, |arg| arg.ctx().unit_term()),
            |func| func.refl(),
            |unit| unit.refl(),
        )
    }

    pub fn equality_of_equality_types(
        eq_term_0_0: &Tm<S>,
        eq_term_1_0: &Tm<S>,
        eq_term_0_1: &Tm<S>,
        eq_term_1_1: &Tm<S>,
    ) -> Iso<S> {
        same_ctx!(eq_term_0_0, eq_term_1_0, eq_term_0_1, eq_term_1_1);
        let ctx = eq_term_0_0.ctx();

        let eq_ty_0 = as_equal(eq_term_0_0.ty(), eq_term_1_0.ty()).unwrap();
        let eq_ty_1 = as_equal(eq_term_0_1.ty(), eq_term_1_1.ty()).unwrap();

        let eq_term_0_0_name = S::name_from_str("val_0_0");
        let eq_term_1_0_name = S::name_from_str("val_1_0");
        let eq_term_0_1_name = S::name_from_str("val_0_1");
        let eq_term_1_1_name = S::name_from_str("val_1_1");

        let tys_eq_name = S::name_from_str("tys_eq");
        let eq_term_0_eq_name = S::name_from_str("val_0_eq");
        let eq_terms_eq_name = S::name_from_str("vals_eq");

        let input_name = S::name_from_str("equality_tys_eq");

        fn generic_scoped<S: Scheme, T: Contextual<S>>(
            ctx: &Ctx<S>,
            func: impl FnOnce(Ty<S>, Ty<S>, Tm<S>, Tm<S>, Tm<S>, Tm<S>) -> T,
        ) -> Scope<S, Scope<S, Scope<S, Scope<S, Scope<S, Scope<S, T>>>>>> {
            ctx
            .universe()
            .scope(|eq_ty_0| {
                let eq_ty_0 = eq_ty_0.to_ty();

                eq_ty_0
                .ctx()
                .universe()
                .scope(|eq_ty_1| {
                    same_ctx!(&eq_ty_0, &eq_ty_1);
                    let eq_ty_1 = eq_ty_1.to_ty();

                    eq_ty_0
                    .scope(|eq_term_0_0| {
                        same_ctx!(&eq_ty_0, &eq_term_0_0);

                        eq_ty_0
                        .scope(|eq_term_1_0| {
                            same_ctx!(&eq_ty_1, &eq_term_1_0);

                            eq_ty_1
                            .scope(|eq_term_0_1| {
                                same_ctx!(&eq_ty_1, &eq_term_0_1);

                                eq_ty_1
                                .scope(|eq_term_1_1| {
                                    same_ctx!(
                                        &eq_ty_0,
                                        &eq_ty_1,
                                        &eq_term_0_0,
                                        &eq_term_1_0,
                                        &eq_term_0_1,
                                        &eq_term_1_1,
                                    );
                                    func(
                                        eq_ty_0,
                                        eq_ty_1,
                                        eq_term_0_0,
                                        eq_term_1_0,
                                        eq_term_0_1,
                                        eq_term_1_1,
                                    )
                                })
                            })
                        })
                    })
                })
            })
        }

        let input_ty = generic_scoped(
            &ctx,
            |_eq_ty_0, _eq_ty_1, eq_term_0_0, eq_term_1_0, eq_term_0_1, eq_term_1_1| {
                eq_term_0_0
                .equals(&eq_term_1_0)
                .to_term()
                .equals(
                    &eq_term_0_1
                    .equals(&eq_term_1_1)
                    .to_term()
                )
            },
        );

        let eq_terms_eq_ty = generic_scoped(
            &ctx,
            |eq_ty_0, eq_ty_1, eq_term_0_0, eq_term_1_0, eq_term_0_1, eq_term_1_1| {
                eq_ty_0
                .to_term()
                .equals(&eq_ty_1.to_term())
                .scope(|tys_eq| {
                    tys_eq
                    .cong(
                        |eq_ty_0, eq_ty_1, _tys_eq| {
                            let eq_ty_0 = eq_ty_0.to_ty();
                            let eq_ty_1 = eq_ty_1.to_ty();

                            eq_ty_0
                            .pi(&eq_term_0_0_name, |eq_term_0_0| {

                                eq_ty_0
                                .weaken_into(&eq_term_0_0.ctx())
                                .pi(&eq_term_1_0_name, |eq_term_1_0| {

                                    eq_ty_1
                                    .weaken_into(&eq_term_1_0.ctx())
                                    .pi(&eq_term_0_1_name, |eq_term_0_1| {

                                        eq_ty_1
                                        .weaken_into(&eq_term_0_1.ctx())
                                        .pi(&eq_term_1_1_name, |eq_term_1_1| {
                                            eq_term_1_1
                                            .ctx()
                                            .universe()
                                        })
                                    })
                                })
                            })
                        },
                        |eq_ty| {
                            let eq_ty = eq_ty.to_ty();

                            eq_ty
                            .func(&eq_term_0_0_name, |eq_term_0_0| {
                                same_ctx!(&eq_ty, &eq_term_0_0);

                                eq_ty
                                .func(&eq_term_1_0_name, |eq_term_1_0| {
                                    same_ctx!(&eq_ty, &eq_term_1_0);

                                    eq_ty
                                    .func(&eq_term_0_1_name, |eq_term_0_1| {
                                        same_ctx!(&eq_ty, &eq_term_0_1);

                                        eq_ty
                                        .func(&eq_term_1_1_name, |eq_term_1_1| {
                                            same_ctx!(&eq_term_0_0, &eq_term_1_1);

                                            eq_term_0_0
                                            .equals(&eq_term_0_1)
                                            .sigma(
                                                &eq_term_0_eq_name,
                                                |_| {
                                                    eq_term_1_0
                                                    .equals(&eq_term_1_1)
                                                },
                                            )
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
                })
            },
        );

        let output_ty = generic_scoped(
            &ctx,
            |eq_ty_0, eq_ty_1, eq_term_0_0, eq_term_1_0, eq_term_0_1, eq_term_1_1| {
                eq_ty_0
                .to_term()
                .equals(&eq_ty_1.to_term())
                .sigma(
                    &tys_eq_name,
                    eq_terms_eq_ty
                    .bind(&eq_ty_0.to_term())
                    .bind(&eq_ty_1.to_term())
                    .bind(&eq_term_0_0)
                    .bind(&eq_term_1_0)
                    .bind(&eq_term_0_1)
                    .bind(&eq_term_1_1)
                    .unbind(),
                )
            },
        );

        let fwd = generic_scoped(
            &ctx,
            |eq_ty_0, eq_ty_1, eq_term_0_0, eq_term_1_0, eq_term_0_1, eq_term_1_1| {
                input_ty
                .bind(&eq_ty_0.to_term())
                .bind(&eq_ty_1.to_term())
                .bind(&eq_term_0_0)
                .bind(&eq_term_1_0)
                .bind(&eq_term_0_1)
                .bind(&eq_term_1_1)
                .scope(|input| {
                    input
                    .equal_eq_eq_ty_injective()
                    .cong(
                        |eq_ty_0, eq_ty_1, _tys_eq| {
                            let eq_ty_0 = eq_ty_0.to_ty();
                            let eq_ty_1 = eq_ty_1.to_ty();

                            eq_ty_0
                            .pi(&eq_term_0_0_name, |eq_term_0_0| {
                                same_ctx!(&eq_ty_0, &eq_term_0_0);

                                eq_ty_0
                                .pi(&eq_term_1_0_name, |eq_term_1_0| {
                                    same_ctx!(&eq_ty_1, &eq_term_1_0);

                                    eq_ty_1
                                    .pi(&eq_term_0_1_name, |eq_term_0_1| {
                                        same_ctx!(&eq_ty_1, &eq_term_0_1);

                                        eq_ty_1
                                        .pi(&eq_term_1_1_name, |eq_term_1_1| {
                                            input_ty
                                            .bind(&eq_ty_0.to_term())
                                            .bind(&eq_ty_1.to_term())
                                            .bind(&eq_term_0_0)
                                            .bind(&eq_term_1_0)
                                            .bind(&eq_term_0_1)
                                            .bind(&eq_term_1_1)
                                            .pi(&input_name, |_input| {
                                                output_ty
                                                .bind(&eq_ty_0.to_term())
                                                .bind(&eq_ty_1.to_term())
                                                .bind(&eq_term_0_0)
                                                .bind(&eq_term_1_0)
                                                .bind(&eq_term_0_1)
                                                .bind(&eq_term_1_1)
                                            })
                                        })
                                    })
                                })
                            })
                        },
                        |eq_ty| {
                            let eq_ty = eq_ty.to_ty();

                            eq_ty
                            .func(&eq_term_0_0_name, |eq_term_0_0| {
                                same_ctx!(&eq_ty, &eq_term_0_0);

                                eq_ty
                                .func(&eq_term_1_0_name, |eq_term_1_0| {
                                    same_ctx!(&eq_ty, &eq_term_1_0);

                                    eq_ty
                                    .func(&eq_term_0_1_name, |eq_term_0_1| {
                                        same_ctx!(&eq_ty, &eq_term_0_1);

                                        eq_ty
                                        .func(&eq_term_1_1_name, |eq_term_1_1| {
                                            input_ty
                                            .bind(&eq_ty.to_term())
                                            .bind(&eq_ty.to_term())
                                            .bind(&eq_term_0_0)
                                            .bind(&eq_term_1_0)
                                            .bind(&eq_term_0_1)
                                            .bind(&eq_term_1_1)
                                            .func(&input_name, |input| {
                                                same_ctx!(&eq_ty, &input);

                                                eq_ty
                                                .to_term()
                                                .refl()
                                                .pair(
                                                    &tys_eq_name,
                                                    eq_terms_eq_ty
                                                    .bind(&eq_ty.to_term())
                                                    .bind(&eq_ty.to_term())
                                                    .bind(&eq_term_0_0)
                                                    .bind(&eq_term_1_0)
                                                    .bind(&eq_term_0_1)
                                                    .bind(&eq_term_1_1)
                                                    .unbind(),
                                                    &input
                                                    .equal_eq_eq_term_0_injective()
                                                    .pair(
                                                        &eq_term_0_eq_name,
                                                        |_| {
                                                            eq_term_1_0
                                                            .equals(&eq_term_1_1)
                                                        },
                                                        &input
                                                        .equal_eq_eq_term_1_injective(),
                                                    )
                                                )
                                            })
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
                    .app(&input)
                })
            },
        );

        let rev = generic_scoped(
            &ctx,
            |eq_ty_0, eq_ty_1, eq_term_0_0, eq_term_1_0, eq_term_0_1, eq_term_1_1| {
                output_ty
                .bind(&eq_ty_0.to_term())
                .bind(&eq_ty_1.to_term())
                .bind(&eq_term_0_0)
                .bind(&eq_term_1_0)
                .bind(&eq_term_0_1)
                .bind(&eq_term_1_1)
                .scope(|output| {
                    let tys_eq = output.proj_head();
                    let eq_terms_eq = output.proj_tail();

                    tys_eq
                    .cong(
                        |eq_ty_0, eq_ty_1, tys_eq| {
                            let eq_ty_0 = eq_ty_0.to_ty();
                            let eq_ty_1 = eq_ty_1.to_ty();

                            eq_ty_0
                            .pi(&eq_term_0_0_name, |eq_term_0_0| {
                                same_ctx!(&eq_ty_0, &eq_term_0_0);

                                eq_ty_0
                                .pi(&eq_term_1_0_name, |eq_term_1_0| {
                                    same_ctx!(&eq_ty_1, &eq_term_1_0);

                                    eq_ty_1
                                    .pi(&eq_term_0_1_name, |eq_term_0_1| {
                                        same_ctx!(&eq_ty_1, &eq_term_0_1);

                                        eq_ty_1
                                        .pi(&eq_term_1_1_name, |eq_term_1_1| {
                                            eq_terms_eq_ty
                                            .bind(&eq_ty_0.to_term())
                                            .bind(&eq_ty_1.to_term())
                                            .bind(&eq_term_0_0)
                                            .bind(&eq_term_1_0)
                                            .bind(&eq_term_0_1)
                                            .bind(&eq_term_1_1)
                                            .bind(&tys_eq)
                                            .pi(&eq_terms_eq_name, |_eq_terms_eq| {
                                                input_ty
                                                .bind(&eq_ty_0.to_term())
                                                .bind(&eq_ty_1.to_term())
                                                .bind(&eq_term_0_0)
                                                .bind(&eq_term_1_0)
                                                .bind(&eq_term_0_1)
                                                .bind(&eq_term_1_1)
                                            })
                                        })
                                    })
                                })
                            })
                        },
                        |eq_ty| {
                            let eq_ty = eq_ty.to_ty();

                            eq_ty
                            .func(&eq_term_0_0_name, |eq_term_0_0| {
                                same_ctx!(&eq_ty, &eq_term_0_0);

                                eq_ty
                                .func(&eq_term_1_0_name, |eq_term_1_0| {
                                    same_ctx!(&eq_ty, &eq_term_1_0);

                                    eq_ty
                                    .func(&eq_term_0_1_name, |eq_term_0_1| {
                                        same_ctx!(&eq_ty, &eq_term_0_1);

                                        eq_ty
                                        .func(&eq_term_1_1_name, |eq_term_1_1| {
                                            eq_terms_eq_ty
                                            .bind(&eq_ty.to_term())
                                            .bind(&eq_ty.to_term())
                                            .bind(&eq_term_0_0)
                                            .bind(&eq_term_1_0)
                                            .bind(&eq_term_0_1)
                                            .bind(&eq_term_1_1)
                                            .bind(&eq_ty.to_term().refl())
                                            .func(&eq_terms_eq_name, |eq_terms_eq| {
                                                let eq_term_0_eq = eq_terms_eq.proj_head();
                                                let eq_term_1_eq = eq_terms_eq.proj_tail();

                                                Tm::map_eqs(
                                                    [&eq_term_0_eq, &eq_term_1_eq],
                                                    |[eq_term_0, eq_term_1]| {
                                                        eq_term_0
                                                        .equals(&eq_term_1)
                                                        .to_term()
                                                    },
                                                )
                                            })
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
                    .app(&eq_terms_eq)
                })
            },
        );

        let fwd_rev = {
            input_ty
            .bind(&eq_ty_0.to_term())
            .bind(&eq_ty_1.to_term())
            .bind(&eq_term_0_0)
            .bind(&eq_term_1_0)
            .bind(&eq_term_0_1)
            .bind(&eq_term_1_1)
            .scope(|input| {
                rev
                .bind(&eq_ty_0.to_term())
                .bind(&eq_ty_1.to_term())
                .bind(&eq_term_0_0)
                .bind(&eq_term_1_0)
                .bind(&eq_term_0_1)
                .bind(&eq_term_1_1)
                .bind(
                    &fwd
                    .bind(&eq_ty_0.to_term())
                    .bind(&eq_ty_1.to_term())
                    .bind(&eq_term_0_0)
                    .bind(&eq_term_1_0)
                    .bind(&eq_term_0_1)
                    .bind(&eq_term_1_1)
                    .bind(&input)
                )
                .equality_contractible(&input)
            })
        };

        let rev_fwd = {
            output_ty
            .bind(&eq_ty_0.to_term())
            .bind(&eq_ty_1.to_term())
            .bind(&eq_term_0_0)
            .bind(&eq_term_1_0)
            .bind(&eq_term_0_1)
            .bind(&eq_term_1_1)
            .scope(|output| {
                let tys_eq = output.proj_head();
                let eq_terms_eq = output.proj_tail();

                tys_eq
                .cong(
                    |eq_ty_0, eq_ty_1, tys_eq| {
                        let eq_ty_0 = eq_ty_0.to_ty();
                        let eq_ty_1 = eq_ty_1.to_ty();

                        eq_ty_0
                        .pi(&eq_term_0_0_name, |eq_term_0_0| {
                            same_ctx!(&eq_ty_0, &eq_term_0_0);

                            eq_ty_0
                            .pi(&eq_term_1_0_name, |eq_term_1_0| {
                                same_ctx!(&eq_ty_1, &eq_term_1_0);

                                eq_ty_1
                                .pi(&eq_term_0_1_name, |eq_term_0_1| {
                                    same_ctx!(&eq_ty_1, &eq_term_0_1);

                                    eq_ty_1
                                    .pi(&eq_term_1_1_name, |eq_term_1_1| {
                                        eq_terms_eq_ty
                                        .bind(&eq_ty_0.to_term())
                                        .bind(&eq_ty_1.to_term())
                                        .bind(&eq_term_0_0)
                                        .bind(&eq_term_1_0)
                                        .bind(&eq_term_0_1)
                                        .bind(&eq_term_1_1)
                                        .bind(&tys_eq)
                                        .pi(&eq_terms_eq_name, |eq_terms_eq| {
                                            let output = {
                                                tys_eq
                                                .pair(
                                                    &tys_eq_name,
                                                    eq_terms_eq_ty
                                                    .bind(&eq_ty_0.to_term())
                                                    .bind(&eq_ty_1.to_term())
                                                    .bind(&eq_term_0_0)
                                                    .bind(&eq_term_1_0)
                                                    .bind(&eq_term_0_1)
                                                    .bind(&eq_term_1_1)
                                                    .unbind(),
                                                    &eq_terms_eq,
                                                )
                                            };

                                            fwd
                                            .bind(&eq_ty_0.to_term())
                                            .bind(&eq_ty_1.to_term())
                                            .bind(&eq_term_0_0)
                                            .bind(&eq_term_1_0)
                                            .bind(&eq_term_0_1)
                                            .bind(&eq_term_1_1)
                                            .bind(
                                                &rev
                                                .bind(&eq_ty_0.to_term())
                                                .bind(&eq_ty_1.to_term())
                                                .bind(&eq_term_0_0)
                                                .bind(&eq_term_1_0)
                                                .bind(&eq_term_0_1)
                                                .bind(&eq_term_1_1)
                                                .bind(&output)
                                            )
                                            .equals(&output)
                                        })
                                    })
                                })
                            })
                        })
                    },
                    |eq_ty| {
                        let eq_ty = eq_ty.to_ty();

                        eq_ty
                        .func(&eq_term_0_0_name, |eq_term_0_0| {
                            same_ctx!(&eq_ty, &eq_term_0_0);

                            eq_ty
                            .func(&eq_term_1_0_name, |eq_term_1_0| {
                                same_ctx!(&eq_ty, &eq_term_1_0);

                                eq_ty
                                .func(&eq_term_0_1_name, |eq_term_0_1| {
                                    same_ctx!(&eq_ty, &eq_term_0_1);

                                    eq_ty
                                    .func(&eq_term_1_1_name, |eq_term_1_1| {
                                        eq_terms_eq_ty
                                        .bind(&eq_ty.to_term())
                                        .bind(&eq_ty.to_term())
                                        .bind(&eq_term_0_0)
                                        .bind(&eq_term_1_0)
                                        .bind(&eq_term_0_1)
                                        .bind(&eq_term_1_1)
                                        .bind(&eq_ty.to_term().refl())
                                        .func(&eq_terms_eq_name, |eq_terms_eq| {
                                            let eq_term_0_eq = eq_terms_eq.proj_head();
                                            let eq_term_1_eq = eq_terms_eq.proj_tail();

                                            eq_term_0_eq
                                            .cong(
                                                |eq_term_0_0, eq_term_0_1, eq_term_0_eq| {
                                                    let output = {
                                                        eq_ty
                                                        .to_term()
                                                        .refl()
                                                        .pair(
                                                            &tys_eq_name,
                                                            eq_terms_eq_ty
                                                            .bind(&eq_ty.to_term())
                                                            .bind(&eq_ty.to_term())
                                                            .bind(&eq_term_0_0)
                                                            .bind(&eq_term_1_0)
                                                            .bind(&eq_term_0_1)
                                                            .bind(&eq_term_1_1)
                                                            .unbind(),
                                                            &eq_term_0_eq
                                                            .pair(
                                                                &eq_term_0_eq_name,
                                                                |_| {
                                                                    eq_term_1_0
                                                                    .equals(&eq_term_1_1)
                                                                },
                                                                &eq_term_1_eq,
                                                            )
                                                        )
                                                    };

                                                    fwd
                                                    .bind(&eq_ty.to_term())
                                                    .bind(&eq_ty.to_term())
                                                    .bind(&eq_term_0_0)
                                                    .bind(&eq_term_1_0)
                                                    .bind(&eq_term_0_1)
                                                    .bind(&eq_term_1_1)
                                                    .bind(
                                                        &rev
                                                        .bind(&eq_ty.to_term())
                                                        .bind(&eq_ty.to_term())
                                                        .bind(&eq_term_0_0)
                                                        .bind(&eq_term_1_0)
                                                        .bind(&eq_term_0_1)
                                                        .bind(&eq_term_1_1)
                                                        .bind(&output)
                                                    )
                                                    .equals(&output)
                                                },
                                                |eq_term_0| {
                                                    same_ctx!(&eq_term_0, &eq_term_1_eq);

                                                    eq_term_1_eq
                                                    .cong(
                                                        |eq_term_1_0, eq_term_1_1, eq_term_1_eq| {
                                                            let output = {
                                                                eq_ty
                                                                .to_term()
                                                                .refl()
                                                                .pair(
                                                                    &tys_eq_name,
                                                                    eq_terms_eq_ty
                                                                    .bind(&eq_ty.to_term())
                                                                    .bind(&eq_ty.to_term())
                                                                    .bind(&eq_term_0)
                                                                    .bind(&eq_term_1_0)
                                                                    .bind(&eq_term_0)
                                                                    .bind(&eq_term_1_1)
                                                                    .unbind(),
                                                                    &eq_term_0
                                                                    .refl()
                                                                    .pair(
                                                                        &eq_term_0_eq_name,
                                                                        |_| {
                                                                            eq_term_1_0
                                                                            .equals(&eq_term_1_1)
                                                                        },
                                                                        &eq_term_1_eq,
                                                                    )
                                                                )
                                                            };

                                                            fwd
                                                            .bind(&eq_ty.to_term())
                                                            .bind(&eq_ty.to_term())
                                                            .bind(&eq_term_0)
                                                            .bind(&eq_term_1_0)
                                                            .bind(&eq_term_0)
                                                            .bind(&eq_term_1_1)
                                                            .bind(
                                                                &rev
                                                                .bind(&eq_ty.to_term())
                                                                .bind(&eq_ty.to_term())
                                                                .bind(&eq_term_0)
                                                                .bind(&eq_term_1_0)
                                                                .bind(&eq_term_0)
                                                                .bind(&eq_term_1_1)
                                                                .bind(&output)
                                                            )
                                                            .equals(&output)
                                                        },
                                                        |eq_term_1| {
                                                            eq_ty
                                                            .to_term()
                                                            .refl()
                                                            .pair(
                                                                &tys_eq_name,
                                                                eq_terms_eq_ty
                                                                .bind(&eq_ty.to_term())
                                                                .bind(&eq_ty.to_term())
                                                                .bind(&eq_term_0)
                                                                .bind(&eq_term_1)
                                                                .bind(&eq_term_0)
                                                                .bind(&eq_term_1)
                                                                .unbind(),
                                                                &eq_term_0
                                                                .refl()
                                                                .pair(
                                                                    &eq_term_0_eq_name,
                                                                    |_| {
                                                                        eq_term_1
                                                                        .equals(&eq_term_1)
                                                                    },
                                                                    &eq_term_1.refl(),
                                                                )
                                                            )
                                                            .refl()
                                                        },
                                                    )
                                                },
                                            )
                                        })
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
                .app(&eq_terms_eq)
            })
        };

        let input_ty = {
            input_ty
            .bind(&eq_ty_0.to_term())
            .bind(&eq_ty_1.to_term())
            .bind(&eq_term_0_0)
            .bind(&eq_term_1_0)
            .bind(&eq_term_0_1)
            .bind(&eq_term_1_1)
        };
        let output_ty = {
            output_ty
            .bind(&eq_ty_0.to_term())
            .bind(&eq_ty_1.to_term())
            .bind(&eq_term_0_0)
            .bind(&eq_term_1_0)
            .bind(&eq_term_0_1)
            .bind(&eq_term_1_1)
        };
        let fwd = {
            fwd
            .bind(&eq_ty_0.to_term())
            .bind(&eq_ty_1.to_term())
            .bind(&eq_term_0_0)
            .bind(&eq_term_1_0)
            .bind(&eq_term_0_1)
            .bind(&eq_term_1_1)
        };
        let rev = {
            rev
            .bind(&eq_ty_0.to_term())
            .bind(&eq_ty_1.to_term())
            .bind(&eq_term_0_0)
            .bind(&eq_term_1_0)
            .bind(&eq_term_0_1)
            .bind(&eq_term_1_1)
        };

        Iso::new(
            &input_ty,
            &output_ty,
            fwd.unbind(),
            rev.unbind(),
            fwd_rev.unbind(),
            rev_fwd.unbind(),
        )
    }


    pub fn equality_of_sum_types_to_equality_of_type_parameters(
        lhs_name_0: &Name<S>,
        lhs_name_1: &Name<S>,
        lhs_ty_0: &Ty<S>,
        lhs_ty_1: &Ty<S>,
        rhs_ty_0: &Ty<S>,
        rhs_ty_1: &Ty<S>,
    ) -> Iso<S> {
        same_ctx!(lhs_name_0, lhs_name_1, lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1);

        let lhs_name_eq_name = S::name_from_str("lhs_name_eq");
        let lhs_ty_eq_name = S::name_from_str("lhs_ty_eq");

        let input_ty = {
            lhs_ty_0
            .sum(&lhs_name_0, &rhs_ty_0)
            .to_term()
            .equals(&lhs_ty_1.sum(&lhs_name_1, &rhs_ty_1).to_term())
        };
        let output_ty = {
            lhs_name_0
            .to_term()
            .equals(&lhs_name_1.to_term())
            .sigma(&lhs_name_eq_name, |_| {
                lhs_ty_0
                .to_term()
                .equals(&lhs_ty_1.to_term())
                .sigma(&lhs_ty_eq_name, |_| {
                    rhs_ty_0.to_term().equals(&rhs_ty_1.to_term())
                })
            })
        };

        let fwd = input_ty.scope(|sum_ty_eq| {
            sum_ty_eq
            .sum_eq_name_injective()
            .pair(
                &lhs_name_eq_name,
                |_| {
                    lhs_ty_0
                    .to_term()
                    .equals(&lhs_ty_1.to_term())
                    .sigma(&lhs_ty_eq_name, |_| {
                        rhs_ty_0.to_term().equals(&rhs_ty_1.to_term())
                    })
                },
                &sum_ty_eq
                .sum_eq_lhs_injective()
                .pair(
                    &lhs_ty_eq_name,
                    |_| rhs_ty_0.to_term().equals(&rhs_ty_1.to_term()),
                    &sum_ty_eq.sum_eq_rhs_injective(),
                ),
            )
        });

        let rev = output_ty.scope(|eq_components| {
            let lhs_name_eq = eq_components.proj_head();
            let lhs_ty_eq = eq_components.proj_tail().proj_head();
            let rhs_ty_eq = eq_components.proj_tail().proj_tail();

            lhs_name_eq
            .cong(
                |lhs_name_0, lhs_name_1, _| {
                    let lhs_name_0 = lhs_name_0.to_name();
                    let lhs_name_1 = lhs_name_1.to_name();

                    lhs_ty_0
                    .sum(&lhs_name_0, &rhs_ty_0)
                    .to_term()
                    .equals(&lhs_ty_1.sum(&lhs_name_1, &rhs_ty_1).to_term())
                },
                |lhs_name| {
                    let lhs_name = lhs_name.to_name();

                    lhs_ty_eq
                    .weaken_into(&lhs_name.ctx())
                    .cong(
                        |lhs_ty_0, lhs_ty_1, _| {
                            let lhs_ty_0 = lhs_ty_0.to_ty();
                            let lhs_ty_1 = lhs_ty_1.to_ty();

                            lhs_ty_0
                            .sum(&lhs_name, &rhs_ty_0)
                            .to_term()
                            .equals(&lhs_ty_1.sum(&lhs_name, &rhs_ty_1).to_term())
                        },
                        |lhs_ty| {
                            let lhs_ty = lhs_ty.to_ty();

                            rhs_ty_eq
                            .weaken_into(&lhs_ty.ctx())
                            .map_eq(|rhs_ty| {
                                let rhs_ty = rhs_ty.to_ty();
                                lhs_ty.sum(&lhs_name, &rhs_ty).to_term()
                            })
                        },
                    )
                },
            )
        });

        let fwd_rev = input_ty.scope(|sum_ty_eq| {
            rev.bind(&fwd.bind(&sum_ty_eq)).equality_contractible(&sum_ty_eq)
        });

        let rev_fwd = output_ty.scope(|eq_components| {
            let eq_components_rev_fwd = fwd.bind(&rev.bind(&eq_components));

            let lhs_name_eq = eq_components.proj_head();
            let lhs_ty_eq = eq_components.proj_tail().proj_head();
            let rhs_ty_eq = eq_components.proj_tail().proj_tail();
            let lhs_name_eq_rev_fwd = eq_components_rev_fwd.proj_head();
            let lhs_ty_eq_rev_fwd = eq_components_rev_fwd.proj_tail().proj_head();
            let rhs_ty_eq_rev_fwd = eq_components_rev_fwd.proj_tail().proj_tail();

            let lhs_name_eq_eq = lhs_name_eq_rev_fwd.equality_contractible(&lhs_name_eq);
            let lhs_ty_eq_eq = lhs_ty_eq_rev_fwd.equality_contractible(&lhs_ty_eq);
            let rhs_ty_eq_eq = rhs_ty_eq_rev_fwd.equality_contractible(&rhs_ty_eq);

            Tm::map_eqs(
                [&lhs_name_eq_eq, &lhs_ty_eq_eq, &rhs_ty_eq_eq],
                |[lhs_name_eq, lhs_ty_eq, rhs_ty_eq]| {
                    lhs_name_eq
                    .pair(
                        &lhs_name_eq_name,
                        |_| {
                            lhs_ty_0
                            .to_term()
                            .equals(&lhs_ty_1.to_term())
                            .sigma(&lhs_ty_eq_name, |_| {
                                rhs_ty_0.to_term().equals(&rhs_ty_1.to_term())
                            })
                        },
                        &lhs_ty_eq
                        .pair(
                            &lhs_ty_eq_name,
                            |_| rhs_ty_0.to_term().equals(&rhs_ty_1.to_term()),
                            &rhs_ty_eq,
                        )
                    )
                },
            )

            /*
            ty_eq_pair_rev_fwd
            .proj_head()
            .equality_contractible(&ty_eq_pair.proj_head())
            .cong(
                |lhs_ty_eq_0, lhs_ty_eq_1, _| {
                    lhs_ty_eq_0
                    .pair(
                        |_| rhs_ty_0.to_term().equals(&rhs_ty_1.to_term()),
                        &ty_eq_pair_rev_fwd.proj_tail(),
                    )
                    .equals(
                        &lhs_ty_eq_1
                        .pair(
                            |_| rhs_ty_0.to_term().equals(&rhs_ty_1.to_term()),
                            &ty_eq_pair.proj_tail(),
                        )
                    )
                },
                |lhs_ty_eq| {
                    ty_eq_pair_rev_fwd
                    .proj_tail()
                    .equality_contractible(&ty_eq_pair.proj_tail())
                    .weaken_into(&lhs_ty_eq.ctx())
                    .map_eq(|rhs_ty_eq| {
                        lhs_ty_eq
                        .weaken_into(&rhs_ty_eq.ctx())
                        .pair(
                            |_| rhs_ty_0.to_term().equals(&rhs_ty_1.to_term()),
                            &rhs_ty_eq,
                        )
                    })
                },
            )
            */
        });

        Iso::new(
            &input_ty,
            &output_ty,
            fwd.unbind(),
            rev.unbind(),
            fwd_rev.unbind(),
            rev_fwd.unbind(),
        )
    }

    /*
    pub fn equality_of_sigma_types_to_equality_of_type_parameters(
        tail_ty_0: &Scope<S, Ty<S>>,
        tail_ty_1: &Scope<S, Ty<S>>,
    ) -> Iso<S> {
        let input_ty = tail_ty_0.to_sigma().to_term().equals(&tail_ty_1.to_sigma().to_term());
        let output_ty = {
            tail_ty_0
            .var_ty()
            .to_term()
            .equals(&tail_ty_1.var_ty().to_term())
            .sigma(|head_ty_eq| {
                head_ty_eq
                .scoped_tys_equal(tail_ty_0.unbind(), tail_ty_1.unbind())
            })
        };

        let fwd = input_ty.scope(|sigma_ty_eq| {
            sigma_ty_eq
            .sigma_eq_head_injective()
            .pair(
                |head_ty_eq| {
                    head_ty_eq
                    .scoped_tys_equal(tail_ty_0.unbind(), tail_ty_1.unbind())
                },
                &sigma_ty_eq
                .sigma_eq_tail_injective(),
            )
        });

        let rev = output_ty.scope(|eq_pair| {
            eq_pair
            .proj_head()
            .cong(
                |head_ty_0, head_ty_1, head_ty_eq| {
                    head_ty_0
                    .to_ty()
                    .pi(|head_0| head_0.ctx().universe())
                    .pi(|tail_ty_0| {
                        head_ty_1
                        .to_ty()
                        .weaken_into(&tail_ty_0.ctx())
                        .pi(|head_1| head_1.ctx().universe())
                        .pi(|tail_ty_1| {
                            head_ty_eq
                            .weaken_into(&tail_ty_1.ctx())
                            .scoped_tys_equal(
                                |head_0| tail_ty_0.app(&head_0).to_ty(),
                                |head_1| tail_ty_1.app(&head_1).to_ty(),
                            )
                            .pi(|tail_ty_eq| {
                                head_ty_0
                                .weaken_into(&tail_ty_eq.ctx())
                                .to_ty()
                                .sigma(|head_0| tail_ty_0.app(&head_0).to_ty())
                                .to_term()
                                .equals(
                                    &head_ty_1
                                    .weaken_into(&tail_ty_eq.ctx())
                                    .to_ty()
                                    .sigma(|head_1| tail_ty_1.app(&head_1).to_ty())
                                    .to_term()
                                )
                            })
                        })
                    })
                },
                |head_ty| {
                    head_ty
                    .to_ty()
                    .pi(|head| head.ctx().universe())
                    .func(|tail_ty_0| {
                        head_ty
                        .weaken_into(&tail_ty_0.ctx())
                        .to_ty()
                        .pi(|head| head.ctx().universe())
                        .func(|tail_ty_1| {
                            tail_ty_0
                            .equals(&tail_ty_1)
                            .func(|tail_ty_eq| {
                                tail_ty_eq
                                .map_eq(|tail_ty| {
                                    head_ty
                                    .weaken_into(&tail_ty.ctx())
                                    .to_ty()
                                    .sigma(|head| tail_ty.app(&head).to_ty())
                                    .to_term()
                                })
                            })
                        })
                    })
                },
            )
            .app(&tail_ty_0.map(|_, tail_ty| tail_ty.to_term()).to_func())
            .app(&tail_ty_1.map(|_, tail_ty| tail_ty.to_term()).to_func())
            .app(&eq_pair.proj_tail())
        });

        let fwd_rev = input_ty.scope(|sigma_ty_eq| {
            rev
            .bind(&fwd.bind(&sigma_ty_eq))
            .equality_contractible(&sigma_ty_eq)
        });

        let rev_fwd = output_ty.scope(|eq_pair| {
            let eq_pair_rev_fwd = fwd.bind(&rev.bind(&eq_pair));

            eq_pair_rev_fwd
            .proj_head()
            .equality_contractible(&eq_pair.proj_head())
            .cong(
                |head_ty_eq_0, head_ty_eq_1, _| {
                    head_ty_eq_0
                    .scoped_tys_equal(tail_ty_0.unbind(), tail_ty_1.unbind())
                    .pi(|tail_ty_eq_0| {
                        head_ty_eq_1
                        .weaken_into(&tail_ty_eq_0.ctx())
                        .scoped_tys_equal(tail_ty_0.unbind(), tail_ty_1.unbind())
                        .pi(|tail_ty_eq_1| {
                            head_ty_eq_0
                            .weaken_into(&tail_ty_eq_1.ctx())
                            .pair(
                                |head_ty_eq| {
                                    head_ty_eq
                                    .scoped_tys_equal(tail_ty_0.unbind(), tail_ty_1.unbind())
                                },
                                &tail_ty_eq_0
                            )
                            .equals(
                                &head_ty_eq_1
                                .weaken_into(&tail_ty_eq_1.ctx())
                                .pair(
                                    |head_ty_eq| {
                                        head_ty_eq
                                        .scoped_tys_equal(tail_ty_0.unbind(), tail_ty_1.unbind())
                                    },
                                    &tail_ty_eq_1
                                )
                            )
                        })
                    })
                },
                |head_ty_eq| {
                    head_ty_eq
                    .cong(
                        |head_ty_0, head_ty_1, head_ty_eq| {
                            head_ty_0
                            .to_ty()
                            .pi(|head_0| head_0.ctx().universe())
                            .pi(|tail_ty_0| {
                                head_ty_1
                                .weaken_into(&tail_ty_0.ctx())
                                .to_ty()
                                .pi(|head_1| head_1.ctx().universe())
                                .pi(|tail_ty_1| {
                                    head_ty_eq
                                    .weaken_into(&tail_ty_1.ctx())
                                    .scoped_tys_equal(
                                        |head_0| tail_ty_0.app(&head_0).to_ty(),
                                        |head_1| tail_ty_1.app(&head_1).to_ty(),
                                    )
                                    .pi(|tail_ty_eq_0| {
                                        head_ty_eq
                                        .weaken_into(&tail_ty_eq_0.ctx())
                                        .scoped_tys_equal(
                                            |head_0| tail_ty_0.app(&head_0).to_ty(),
                                            |head_1| tail_ty_1.app(&head_1).to_ty(),
                                        )
                                        .pi(|tail_ty_eq_1| {
                                            head_ty_eq
                                            .weaken_into(&tail_ty_eq_1.ctx())
                                            .pair(
                                                |head_ty_eq| {
                                                    head_ty_eq
                                                    .scoped_tys_equal(
                                                        |head_0| tail_ty_0.app(&head_0).to_ty(),
                                                        |head_1| tail_ty_1.app(&head_1).to_ty(),
                                                    )
                                                },
                                                &tail_ty_eq_0,
                                            )
                                            .equals(
                                                &head_ty_eq
                                                .weaken_into(&tail_ty_eq_1.ctx())
                                                .pair(
                                                    |head_ty_eq| {
                                                        head_ty_eq
                                                        .scoped_tys_equal(
                                                            |head_0| {
                                                                tail_ty_0.app(&head_0).to_ty()
                                                            },
                                                            |head_1| {
                                                                tail_ty_1.app(&head_1).to_ty()
                                                            },
                                                        )
                                                    },
                                                    &tail_ty_eq_1,
                                                )
                                            )
                                        })
                                    })
                                })
                            })
                        },
                        |head_ty| {
                            head_ty
                            .to_ty()
                            .pi(|head| head.ctx().universe())
                            .func(|tail_ty_0| {
                                head_ty
                                .weaken_into(&tail_ty_0.ctx())
                                .to_ty()
                                .pi(|head| head.ctx().universe())
                                .func(|tail_ty_1| {
                                    tail_ty_0
                                    .equals(&tail_ty_1)
                                    .func(|tail_ty_eq_0| {
                                        tail_ty_0
                                        .weaken_into(&tail_ty_eq_0.ctx())
                                        .equals(&tail_ty_1)
                                        .func(|tail_ty_eq_1| {
                                            tail_ty_eq_0
                                            .equality_contractible(&tail_ty_eq_1)
                                            .map_eq(|tail_ty_eq| {
                                                head_ty
                                                .weaken_into(&tail_ty_eq.ctx())
                                                .to_term()
                                                .refl()
                                                .pair(
                                                    |head_ty_eq| {
                                                        head_ty_eq
                                                        .scoped_tys_equal(
                                                            |head_0| {
                                                                tail_ty_0.app(&head_0).to_ty()
                                                            },
                                                            |head_1| {
                                                                tail_ty_1.app(&head_1).to_ty()
                                                            },
                                                        )
                                                    },
                                                    &tail_ty_eq,
                                                )
                                            })
                                        })
                                    })
                                })
                            })
                        },
                    )
                    .app(&tail_ty_0.map(|_, tail_ty_0| tail_ty_0.to_term()).to_func())
                    .app(&tail_ty_1.map(|_, tail_ty_1| tail_ty_1.to_term()).to_func())
                },
            )
            .app(&eq_pair_rev_fwd.proj_tail())
            .app(&eq_pair.proj_tail())
        });

        Iso::new(
            &input_ty,
            &output_ty,
            fwd.unbind(),
            rev.unbind(),
            fwd_rev.unbind(),
            rev_fwd.unbind(),
        )
    }
    */

    pub fn equality_of_sigma_types_to_equality_of_type_parameters(
        head_name_0: &Name<S>,
        head_name_1: &Name<S>,
        head_ty_0: &Ty<S>,
        head_ty_1: &Ty<S>,
        tail_ty_0: impl FnOnce(Tm<S>) -> Ty<S>,
        tail_ty_1: impl FnOnce(Tm<S>) -> Ty<S>,
    ) -> Iso<S> {
        same_ctx!(head_name_0, head_name_1, head_ty_0, head_ty_1);
        let tail_ty_0 = head_ty_0.scope(tail_ty_0);
        let tail_ty_1 = head_ty_1.scope(tail_ty_1);

        let head_name_eq_name = S::name_from_str("head_names_eq");
        let head_ty_eq_name = S::name_from_str("head_tys_eq");
        let tail_ty_0_name = S::name_from_str("tail_ty_0");
        let tail_ty_1_name = S::name_from_str("tail_ty_1");
        let tail_ty_eq_0_name = S::name_from_str("tail_tys_eq_0");
        let tail_ty_eq_1_name = S::name_from_str("tail_tys_eq_1");
        let tail_ty_eq_name = S::name_from_str("tail_tys_eq");

        let input_ty = {
            tail_ty_0
            .to_sigma(&head_name_0)
            .to_term()
            .equals(
                &tail_ty_1
                .to_sigma(&head_name_1)
                .to_term(),
            )
        };

        let tail_ty_eq_ty = {
            head_name_0
            .to_term()
            .equals(&head_name_1.to_term())
            .scope(|head_name_eq| {
                head_ty_0
                .to_term()
                .equals(&head_ty_1.to_term())
                .weaken_into(&head_name_eq.ctx())
                .scope(|head_ty_eq| {
                    Ty::scoped_tys_equal(
                        &head_name_eq,
                        &head_ty_eq,
                        tail_ty_0.unbind(),
                        tail_ty_1.unbind(),
                    )
                })
            })
        };
        let head_and_tail_ty_eq_ty = tail_ty_eq_ty.map(|_, inner| {
            inner.to_sigma(&head_ty_eq_name)
        });
        let output_ty = head_and_tail_ty_eq_ty.to_sigma(&head_name_eq_name);

        let fwd = input_ty.scope(|sigma_ty_eq| {
            sigma_ty_eq
            .sigma_eq_cong(
                |head_name_0, head_name_1, head_ty_0, head_ty_1, tail_ty_0, tail_ty_1, _sigma_ty_eq| {
                    head_name_0
                    .to_term()
                    .equals(&head_name_1.to_term())
                    .sigma(&head_name_eq_name, |head_name_eq| {
                        head_ty_0
                        .to_term()
                        .equals(&head_ty_1.to_term())
                        .weaken_into(&head_name_eq.ctx())
                        .sigma(&head_ty_eq_name, |head_ty_eq| {
                            Ty::scoped_tys_equal(
                                &head_name_eq,
                                &head_ty_eq,
                                |head_0| tail_ty_0.app(&head_0).to_ty(),
                                |head_1| tail_ty_1.app(&head_1).to_ty(),
                            )
                        })
                    })
                },
                |head_name, head_ty, tail_ty| {
                    head_name
                    .to_term()
                    .refl()
                    .pair(
                        &head_name_eq_name,
                        |head_name_eq| {
                            head_ty
                            .to_term()
                            .equals(&head_ty.to_term())
                            .weaken_into(&head_name_eq.ctx())
                            .sigma(&head_ty_eq_name, |head_ty_eq| {
                                Ty::scoped_tys_equal(
                                    &head_name_eq,
                                    &head_ty_eq,
                                    |head| tail_ty.app(&head).to_ty(),
                                    |head| tail_ty.app(&head).to_ty(),
                                )
                            })
                        },
                        &head_ty
                        .to_term()
                        .refl()
                        .pair(
                            &head_ty_eq_name,
                            |head_ty_eq| {
                                Ty::scoped_tys_equal(
                                    &head_name.to_term().refl(),
                                    &head_ty_eq,
                                    |head| tail_ty.app(&head).to_ty(),
                                    |head| tail_ty.app(&head).to_ty(),
                                )
                            },
                            &tail_ty
                            .refl(),
                        )
                    )
                },
            )
        });

        let rev = output_ty.scope(|eq_components| {
            let head_name_eq = eq_components.proj_head();
            let head_ty_eq = eq_components.proj_tail().proj_head();
            let tail_ty_eq = eq_components.proj_tail().proj_tail();

            head_name_eq
            .cong(
                |head_name_0, head_name_1, head_name_eq| {
                    let head_name_0 = head_name_0.to_name();
                    let head_name_1 = head_name_1.to_name();

                    Ty::scoped_tys_equal(
                        &head_name_eq,
                        &head_ty_eq,
                        tail_ty_0.unbind(),
                        tail_ty_1.unbind(),
                    )
                    .pi(&tail_ty_eq_name, |_tail_ty_eq| {
                        tail_ty_0
                        .to_sigma(&head_name_0)
                        .to_term()
                        .equals(&tail_ty_1.to_sigma(&head_name_1).to_term())
                    })
                },
                |head_name| {
                    let head_name = head_name.to_name();

                    head_ty_eq
                    .weaken_into(&head_name.ctx())
                    .cong(
                        |head_ty_0, head_ty_1, head_ty_eq| {
                            let head_ty_0 = head_ty_0.to_ty();
                            let head_ty_1 = head_ty_1.to_ty();

                            head_ty_0
                            .pi(&head_name, |head| head.ctx().universe())
                            .pi(&tail_ty_0_name, |tail_ty_0| {
                                head_ty_1
                                .weaken_into(&tail_ty_0.ctx())
                                .pi(&head_name, |head| head.ctx().universe())
                                .pi(&tail_ty_1_name, |tail_ty_1| {
                                    Ty::scoped_tys_equal(
                                        &head_name.to_term().refl(),
                                        &head_ty_eq.weaken_into(&tail_ty_1.ctx()),
                                        |head_0| tail_ty_0.app(&head_0).to_ty(),
                                        |head_1| tail_ty_1.app(&head_1).to_ty(),
                                    )
                                    .pi(&tail_ty_eq_name, |tail_ty_eq| {
                                        head_ty_0
                                        .weaken_into(&tail_ty_eq.ctx())
                                        .sigma(&head_name, |head_0| tail_ty_0.app(&head_0).to_ty())
                                        .to_term()
                                        .equals(
                                            &head_ty_1
                                            .weaken_into(&tail_ty_eq.ctx())
                                            .sigma(&head_name, |head_1| tail_ty_1.app(&head_1).to_ty())
                                            .to_term()
                                        )
                                    })
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
                                .pi(&head_name, |head| head.ctx().universe())
                                .func(&tail_ty_1_name, |tail_ty_1| {
                                    tail_ty_0
                                    .equals(&tail_ty_1)
                                    .func(&tail_ty_eq_name, |tail_ty_eq| {
                                        tail_ty_eq
                                        .map_eq(|tail_ty| {
                                            head_ty
                                            .weaken_into(&tail_ty.ctx())
                                            .sigma(&head_name, |head| tail_ty.app(&head).to_ty())
                                            .to_term()
                                        })
                                    })
                                })
                            })
                        },
                    )
                    .app(&head_ty_0.func(&head_name, |head| tail_ty_0.bind(&head).to_term()))
                    .app(&head_ty_1.func(&head_name, |head| tail_ty_1.bind(&head).to_term()))
                },
            )
            .app(&tail_ty_eq)
        });

        let fwd_rev = input_ty.scope(|sigma_ty_eq| {
            rev
            .bind(&fwd.bind(&sigma_ty_eq))
            .equality_contractible(&sigma_ty_eq)
        });

        let rev_fwd = output_ty.scope(|eq_components| {
            let eq_components_rev_fwd = fwd.bind(&rev.bind(&eq_components));

            let head_name_eq_0 = eq_components_rev_fwd.proj_head();
            let head_name_eq_1 = eq_components.proj_head();

            let head_ty_eq_0 = eq_components_rev_fwd.proj_tail().proj_head();
            let head_ty_eq_1 = eq_components.proj_tail().proj_head();

            let tail_ty_eq_0 = eq_components_rev_fwd.proj_tail().proj_tail();
            let tail_ty_eq_1 = eq_components.proj_tail().proj_tail();

            let join_components = |head_name_eq: &Tm<S>, head_ty_eq: &Tm<S>, tail_ty_eq: &Tm<S>| {
                same_ctx!(head_name_eq, head_ty_eq, tail_ty_eq);
                head_name_eq
                .pair(
                    &head_name_eq_name,
                    |head_name_eq| {
                        head_ty_0
                        .to_term()
                        .equals(&head_ty_1.to_term())
                        .weaken_into(&head_name_eq.ctx())
                        .sigma(&head_ty_eq_name, |head_ty_eq| {
                            Ty::scoped_tys_equal(
                                &head_name_eq,
                                &head_ty_eq,
                                tail_ty_0.unbind(),
                                tail_ty_1.unbind(),
                            )
                        })
                    },
                    &head_ty_eq
                    .pair(
                        &head_ty_eq_name,
                        |head_ty_eq| {
                            Ty::scoped_tys_equal(
                                &head_name_eq,
                                &head_ty_eq,
                                tail_ty_0.unbind(),
                                tail_ty_1.unbind(),
                            )
                        },
                        &tail_ty_eq,
                    )
                )
            };

            head_name_eq_0
            .equality_contractible(&head_name_eq_1)
            .cong(
                |head_name_eq_0, head_name_eq_1, _| {
                    Ty::scoped_tys_equal(
                        &head_name_eq_0,
                        &head_ty_eq_0,
                        tail_ty_0.unbind(),
                        tail_ty_1.unbind(),
                    )
                    .pi(&tail_ty_eq_0_name, |tail_ty_eq_0| {
                        Ty::scoped_tys_equal(
                            &head_name_eq_1,
                            &head_ty_eq_1,
                            tail_ty_0.unbind(),
                            tail_ty_1.unbind(),
                        )
                        .weaken_into(&tail_ty_eq_0.ctx())
                        .pi(&tail_ty_eq_1_name, |tail_ty_eq_1| {
                            join_components(
                                &head_name_eq_0,
                                &head_ty_eq_0,
                                &tail_ty_eq_0,
                            )
                            .equals(
                                &join_components(
                                    &head_name_eq_1,
                                    &head_ty_eq_1,
                                    &tail_ty_eq_1,
                                )
                            )
                        })
                    })
                },
                |head_name_eq| {
                    head_ty_eq_0
                    .equality_contractible(&head_ty_eq_1)
                    .weaken_into(&head_name_eq.ctx())
                    .cong(
                        |head_ty_eq_0, head_ty_eq_1, _| {
                            Ty::scoped_tys_equal(
                                &head_name_eq,
                                &head_ty_eq_0,
                                tail_ty_0.unbind(),
                                tail_ty_1.unbind(),
                            )
                            .pi(&tail_ty_eq_0_name, |tail_ty_eq_0| {
                                Ty::scoped_tys_equal(
                                    &head_name_eq,
                                    &head_ty_eq_1,
                                    tail_ty_0.unbind(),
                                    tail_ty_1.unbind(),
                                )
                                .weaken_into(&tail_ty_eq_0.ctx())
                                .pi(&tail_ty_eq_1_name, |tail_ty_eq_1| {
                                    join_components(
                                        &head_name_eq,
                                        &head_ty_eq_0,
                                        &tail_ty_eq_0,
                                    )
                                    .equals(
                                        &join_components(
                                            &head_name_eq,
                                            &head_ty_eq_1,
                                            &tail_ty_eq_1,
                                        )
                                    )
                                })
                            })
                        },
                        |head_ty_eq| {
                            Ty::scoped_tys_equal(
                                &head_name_eq,
                                &head_ty_eq,
                                tail_ty_0.unbind(),
                                tail_ty_1.unbind(),
                            )
                            .func(&tail_ty_eq_0_name, |tail_ty_eq_0| {
                                Ty::scoped_tys_equal(
                                    &head_name_eq,
                                    &head_ty_eq,
                                    tail_ty_0.unbind(),
                                    tail_ty_1.unbind(),
                                )
                                .weaken_into(&tail_ty_eq_0.ctx())
                                .func(&tail_ty_eq_1_name, |tail_ty_eq_1| {
                                    Tm::scoped_tys_equal_contractible(
                                        &head_name_eq,
                                        &head_ty_eq,
                                        tail_ty_0.unbind(),
                                        tail_ty_1.unbind(),
                                        &tail_ty_eq_0,
                                        &tail_ty_eq_1,
                                    )
                                    .map_eq(|tail_ty_eq| {
                                        join_components(
                                            &head_name_eq,
                                            &head_ty_eq,
                                            &tail_ty_eq,
                                        )
                                    })
                                })
                            })
                        },
                    )
                },
            )
            .app(&tail_ty_eq_0)
            .app(&tail_ty_eq_1)
        });

        Iso::new(
            &input_ty,
            &output_ty,
            fwd.unbind(),
            rev.unbind(),
            fwd_rev.unbind(),
            rev_fwd.unbind(),
        )
    }

    pub fn equality_of_pi_types_to_equality_of_type_parameters(
        arg_name_0: &Name<S>,
        arg_name_1: &Name<S>,
        arg_ty_0: &Ty<S>,
        arg_ty_1: &Ty<S>,
        res_ty_0: impl FnOnce(Tm<S>) -> Ty<S>,
        res_ty_1: impl FnOnce(Tm<S>) -> Ty<S>,
    ) -> Iso<S> {
        same_ctx!(arg_name_0, arg_name_1, arg_ty_0, arg_ty_1);
        let res_ty_0 = arg_ty_0.scope(res_ty_0);
        let res_ty_1 = arg_ty_1.scope(res_ty_1);

        let arg_name_eq_name = S::name_from_str("arg_names_eq");
        let arg_ty_eq_name = S::name_from_str("arg_tys_eq");
        let res_ty_0_name = S::name_from_str("res_ty_0");
        let res_ty_1_name = S::name_from_str("res_ty_1");
        let res_ty_eq_0_name = S::name_from_str("res_tys_eq_0");
        let res_ty_eq_1_name = S::name_from_str("res_tys_eq_1");
        let res_ty_eq_name = S::name_from_str("res_tys_eq");

        let input_ty = {
            res_ty_0
            .to_pi(&arg_name_0)
            .to_term()
            .equals(
                &res_ty_1
                .to_pi(&arg_name_1)
                .to_term(),
            )
        };

        let res_ty_eq_ty = {
            arg_name_0
            .to_term()
            .equals(&arg_name_1.to_term())
            .scope(|arg_name_eq| {
                arg_ty_0
                .to_term()
                .equals(&arg_ty_1.to_term())
                .weaken_into(&arg_name_eq.ctx())
                .scope(|arg_ty_eq| {
                    Ty::scoped_tys_equal(
                        &arg_name_eq,
                        &arg_ty_eq,
                        res_ty_0.unbind(),
                        res_ty_1.unbind(),
                    )
                })
            })
        };
        let arg_and_res_ty_eq_ty = res_ty_eq_ty.map(|_, inner| {
            inner.to_sigma(&arg_ty_eq_name)
        });
        let output_ty = arg_and_res_ty_eq_ty.to_sigma(&arg_name_eq_name);

        let fwd = input_ty.scope(|pi_ty_eq| {
            pi_ty_eq
            .pi_eq_cong(
                |arg_name_0, arg_name_1, arg_ty_0, arg_ty_1, res_ty_0, res_ty_1, _pi_ty_eq| {
                    arg_name_0
                    .to_term()
                    .equals(&arg_name_1.to_term())
                    .sigma(&arg_name_eq_name, |arg_name_eq| {
                        arg_ty_0
                        .to_term()
                        .equals(&arg_ty_1.to_term())
                        .weaken_into(&arg_name_eq.ctx())
                        .sigma(&arg_ty_eq_name, |arg_ty_eq| {
                            Ty::scoped_tys_equal(
                                &arg_name_eq,
                                &arg_ty_eq,
                                |arg_0| res_ty_0.app(&arg_0).to_ty(),
                                |arg_1| res_ty_1.app(&arg_1).to_ty(),
                            )
                        })
                    })
                },
                |arg_name, arg_ty, res_ty| {
                    arg_name
                    .to_term()
                    .refl()
                    .pair(
                        &arg_name_eq_name,
                        |arg_name_eq| {
                            arg_ty
                            .to_term()
                            .equals(&arg_ty.to_term())
                            .weaken_into(&arg_name_eq.ctx())
                            .sigma(&arg_ty_eq_name, |arg_ty_eq| {
                                Ty::scoped_tys_equal(
                                    &arg_name_eq,
                                    &arg_ty_eq,
                                    |arg| res_ty.app(&arg).to_ty(),
                                    |arg| res_ty.app(&arg).to_ty(),
                                )
                            })
                        },
                        &arg_ty
                        .to_term()
                        .refl()
                        .pair(
                            &arg_ty_eq_name,
                            |arg_ty_eq| {
                                Ty::scoped_tys_equal(
                                    &arg_name.to_term().refl(),
                                    &arg_ty_eq,
                                    |arg| res_ty.app(&arg).to_ty(),
                                    |arg| res_ty.app(&arg).to_ty(),
                                )
                            },
                            &res_ty
                            .refl(),
                        )
                    )
                },
            )
        });

        let rev = output_ty.scope(|eq_components| {
            let arg_name_eq = eq_components.proj_head();
            let arg_ty_eq = eq_components.proj_tail().proj_head();
            let res_ty_eq = eq_components.proj_tail().proj_tail();

            arg_name_eq
            .cong(
                |arg_name_0, arg_name_1, arg_name_eq| {
                    let arg_name_0 = arg_name_0.to_name();
                    let arg_name_1 = arg_name_1.to_name();

                    Ty::scoped_tys_equal(
                        &arg_name_eq,
                        &arg_ty_eq,
                        res_ty_0.unbind(),
                        res_ty_1.unbind(),
                    )
                    .pi(&res_ty_eq_name, |_res_ty_eq| {
                        res_ty_0
                        .to_pi(&arg_name_0)
                        .to_term()
                        .equals(&res_ty_1.to_pi(&arg_name_1).to_term())
                    })
                },
                |arg_name| {
                    let arg_name = arg_name.to_name();

                    arg_ty_eq
                    .weaken_into(&arg_name.ctx())
                    .cong(
                        |arg_ty_0, arg_ty_1, arg_ty_eq| {
                            let arg_ty_0 = arg_ty_0.to_ty();
                            let arg_ty_1 = arg_ty_1.to_ty();

                            arg_ty_0
                            .pi(&arg_name, |arg| arg.ctx().universe())
                            .pi(&res_ty_0_name, |res_ty_0| {
                                arg_ty_1
                                .weaken_into(&res_ty_0.ctx())
                                .pi(&arg_name, |arg| arg.ctx().universe())
                                .pi(&res_ty_1_name, |res_ty_1| {
                                    Ty::scoped_tys_equal(
                                        &arg_name.to_term().refl(),
                                        &arg_ty_eq.weaken_into(&res_ty_1.ctx()),
                                        |arg_0| res_ty_0.app(&arg_0).to_ty(),
                                        |arg_1| res_ty_1.app(&arg_1).to_ty(),
                                    )
                                    .pi(&res_ty_eq_name, |res_ty_eq| {
                                        arg_ty_0
                                        .weaken_into(&res_ty_eq.ctx())
                                        .pi(&arg_name, |arg_0| res_ty_0.app(&arg_0).to_ty())
                                        .to_term()
                                        .equals(
                                            &arg_ty_1
                                            .weaken_into(&res_ty_eq.ctx())
                                            .pi(&arg_name, |arg_1| res_ty_1.app(&arg_1).to_ty())
                                            .to_term()
                                        )
                                    })
                                })
                            })
                        },
                        |arg_ty| {
                            let arg_ty = arg_ty.to_ty();

                            arg_ty
                            .pi(&arg_name, |arg| arg.ctx().universe())
                            .func(&res_ty_0_name, |res_ty_0| {
                                arg_ty
                                .weaken_into(&res_ty_0.ctx())
                                .pi(&arg_name, |arg| arg.ctx().universe())
                                .func(&res_ty_1_name, |res_ty_1| {
                                    res_ty_0
                                    .equals(&res_ty_1)
                                    .func(&res_ty_eq_name, |res_ty_eq| {
                                        res_ty_eq
                                        .map_eq(|res_ty| {
                                            arg_ty
                                            .weaken_into(&res_ty.ctx())
                                            .pi(&arg_name, |arg| res_ty.app(&arg).to_ty())
                                            .to_term()
                                        })
                                    })
                                })
                            })
                        },
                    )
                    .app(&arg_ty_0.func(&arg_name, |arg| res_ty_0.bind(&arg).to_term()))
                    .app(&arg_ty_1.func(&arg_name, |arg| res_ty_1.bind(&arg).to_term()))
                },
            )
            .app(&res_ty_eq)
        });

        let fwd_rev = input_ty.scope(|pi_ty_eq| {
            rev
            .bind(&fwd.bind(&pi_ty_eq))
            .equality_contractible(&pi_ty_eq)
        });

        let rev_fwd = output_ty.scope(|eq_components| {
            let eq_components_rev_fwd = fwd.bind(&rev.bind(&eq_components));

            let arg_name_eq_0 = eq_components_rev_fwd.proj_head();
            let arg_name_eq_1 = eq_components.proj_head();

            let arg_ty_eq_0 = eq_components_rev_fwd.proj_tail().proj_head();
            let arg_ty_eq_1 = eq_components.proj_tail().proj_head();

            let res_ty_eq_0 = eq_components_rev_fwd.proj_tail().proj_tail();
            let res_ty_eq_1 = eq_components.proj_tail().proj_tail();

            let join_components = |arg_name_eq: &Tm<S>, arg_ty_eq: &Tm<S>, res_ty_eq: &Tm<S>| {
                same_ctx!(arg_name_eq, arg_ty_eq, res_ty_eq);
                arg_name_eq
                .pair(
                    &arg_name_eq_name,
                    |arg_name_eq| {
                        arg_ty_0
                        .to_term()
                        .equals(&arg_ty_1.to_term())
                        .weaken_into(&arg_name_eq.ctx())
                        .sigma(&arg_ty_eq_name, |arg_ty_eq| {
                            Ty::scoped_tys_equal(
                                &arg_name_eq,
                                &arg_ty_eq,
                                res_ty_0.unbind(),
                                res_ty_1.unbind(),
                            )
                        })
                    },
                    &arg_ty_eq
                    .pair(
                        &arg_ty_eq_name,
                        |arg_ty_eq| {
                            Ty::scoped_tys_equal(
                                &arg_name_eq,
                                &arg_ty_eq,
                                res_ty_0.unbind(),
                                res_ty_1.unbind(),
                            )
                        },
                        &res_ty_eq,
                    )
                )
            };

            arg_name_eq_0
            .equality_contractible(&arg_name_eq_1)
            .cong(
                |arg_name_eq_0, arg_name_eq_1, _| {
                    Ty::scoped_tys_equal(
                        &arg_name_eq_0,
                        &arg_ty_eq_0,
                        res_ty_0.unbind(),
                        res_ty_1.unbind(),
                    )
                    .pi(&res_ty_eq_0_name, |res_ty_eq_0| {
                        Ty::scoped_tys_equal(
                            &arg_name_eq_1,
                            &arg_ty_eq_1,
                            res_ty_0.unbind(),
                            res_ty_1.unbind(),
                        )
                        .weaken_into(&res_ty_eq_0.ctx())
                        .pi(&res_ty_eq_1_name, |res_ty_eq_1| {
                            join_components(
                                &arg_name_eq_0,
                                &arg_ty_eq_0,
                                &res_ty_eq_0,
                            )
                            .equals(
                                &join_components(
                                    &arg_name_eq_1,
                                    &arg_ty_eq_1,
                                    &res_ty_eq_1,
                                )
                            )
                        })
                    })
                },
                |arg_name_eq| {
                    arg_ty_eq_0
                    .equality_contractible(&arg_ty_eq_1)
                    .weaken_into(&arg_name_eq.ctx())
                    .cong(
                        |arg_ty_eq_0, arg_ty_eq_1, _| {
                            Ty::scoped_tys_equal(
                                &arg_name_eq,
                                &arg_ty_eq_0,
                                res_ty_0.unbind(),
                                res_ty_1.unbind(),
                            )
                            .pi(&res_ty_eq_0_name, |res_ty_eq_0| {
                                Ty::scoped_tys_equal(
                                    &arg_name_eq,
                                    &arg_ty_eq_1,
                                    res_ty_0.unbind(),
                                    res_ty_1.unbind(),
                                )
                                .weaken_into(&res_ty_eq_0.ctx())
                                .pi(&res_ty_eq_1_name, |res_ty_eq_1| {
                                    join_components(
                                        &arg_name_eq,
                                        &arg_ty_eq_0,
                                        &res_ty_eq_0,
                                    )
                                    .equals(
                                        &join_components(
                                            &arg_name_eq,
                                            &arg_ty_eq_1,
                                            &res_ty_eq_1,
                                        )
                                    )
                                })
                            })
                        },
                        |arg_ty_eq| {
                            Ty::scoped_tys_equal(
                                &arg_name_eq,
                                &arg_ty_eq,
                                res_ty_0.unbind(),
                                res_ty_1.unbind(),
                            )
                            .func(&res_ty_eq_0_name, |res_ty_eq_0| {
                                Ty::scoped_tys_equal(
                                    &arg_name_eq,
                                    &arg_ty_eq,
                                    res_ty_0.unbind(),
                                    res_ty_1.unbind(),
                                )
                                .weaken_into(&res_ty_eq_0.ctx())
                                .func(&res_ty_eq_1_name, |res_ty_eq_1| {
                                    Tm::scoped_tys_equal_contractible(
                                        &arg_name_eq,
                                        &arg_ty_eq,
                                        res_ty_0.unbind(),
                                        res_ty_1.unbind(),
                                        &res_ty_eq_0,
                                        &res_ty_eq_1,
                                    )
                                    .map_eq(|res_ty_eq| {
                                        join_components(
                                            &arg_name_eq,
                                            &arg_ty_eq,
                                            &res_ty_eq,
                                        )
                                    })
                                })
                            })
                        },
                    )
                },
            )
            .app(&res_ty_eq_0)
            .app(&res_ty_eq_1)
        });

        Iso::new(
            &input_ty,
            &output_ty,
            fwd.unbind(),
            rev.unbind(),
            fwd_rev.unbind(),
            rev_fwd.unbind(),
        )
    }

    pub fn sigma_tail_ty_constrains_head_ty(
        head_name: &Name<S>,
        tail_ty: impl FnOnce(Tm<S>) -> Ty<S>,
        head_term: &Tm<S>,
        proof: impl FnOnce(Tm<S>, Tm<S>) -> Tm<S>,
        tail_name: &Name<S>,
    ) -> Iso<S> {
        same_ctx!(head_name, head_term, tail_name);
        let head_ty = head_term.ty();
        let tail_ty = head_ty.scope(tail_ty);
        let proof = tail_ty.map(|head, tail_ty| tail_ty.scope(|tail| {
            let head = head.weaken_into(&tail.ctx());
            proof(head, tail)
        }));

        Iso::new(
            &tail_ty.to_sigma(&head_name),
            &tail_ty.bind(&head_term),
            |sigma_term| {
                tail_ty
                .bind_eq(&proof.bind(&sigma_term.proj_head()).bind(&sigma_term.proj_tail()))
                .transport(&sigma_term.proj_tail())
            },
            |tail_term| head_term.pair(&head_name, |head| tail_ty.bind(&head), &tail_term),
            |sigma_term| {
                proof
                .bind(&sigma_term.proj_head())
                .bind(&sigma_term.proj_tail())
                .cong(
                    |head_0, head_1, head_eq| {
                        tail_ty
                        .bind(&head_0)
                        .pi(&tail_name, |tail_term| {
                            head_1
                            .pair(
                                &head_name,
                                |head| tail_ty.bind(&head),
                                &tail_ty.bind_eq(&head_eq).transport(&tail_term),
                            )
                            .equals(
                                &head_0
                                .pair(
                                    &head_name,
                                    |head| tail_ty.bind(&head),
                                    &tail_term,
                                ),
                            )
                        })
                    },
                    |head| {
                        tail_ty
                        .bind(&head)
                        .func(&tail_name, |tail_term| {
                            head.pair(&head_name, |head| tail_ty.bind(&head), &tail_term).refl()
                        })
                    },
                )
                .app(&sigma_term.proj_tail())
            },
            |tail_term| {
                proof
                .bind(&head_term)
                .bind(&tail_term)
                .unique_identity(
                    |head, head_eq| {
                        tail_ty
                        .bind(&head)
                        .pi(&tail_name, |tail_term| {
                            tail_ty
                            .bind_eq(&head_eq)
                            .transport(&tail_term)
                            .equals(&tail_term)
                        })
                    },
                    |head| {
                        tail_ty
                        .bind(&head)
                        .func(&tail_name, |tail_term| tail_term.refl())
                    },
                )
                .app(&tail_term)
            },
        )
    }

    pub fn nat_is_zero_or_succ(ctx: &Ctx<S>) -> Iso<S> {
        let zero_name = S::name_from_str("zero");

        let input_ty = ctx.nat();
        let output_ty = ctx.unit_ty().sum(&zero_name, &ctx.nat());
        
        let fwd = input_ty.scope(|n| {
            n.for_loop(
                |_| output_ty.clone(),
                &n.ctx().unit_term().inj_lhs(&zero_name, &n.ctx().nat()),
                |n, _| n.inj_rhs(&zero_name, &n.ctx().unit_ty()),
            )
        });
        let rev = output_ty.scope(|sum| {
            sum.case(
                |_| input_ty.clone(),
                |unit| unit.ctx().zero(),
                |n| n.succs(1u32),
            )
        });
        let fwd_rev = input_ty.scope(|n| {
            n.for_loop(
                |n| rev.bind(&fwd.bind(&n)).equals(&n),
                &n.ctx().zero().refl(),
                |n, _| n.succs(1u32).refl(),
            )
        });
        let rev_fwd = output_ty.scope(|sum| {
            sum.case(
                |sum| fwd.bind(&rev.bind(&sum)).equals(&sum),
                |unit| unit.inj_lhs(&zero_name, &unit.ctx().nat()).refl(),
                |n| n.inj_rhs(&zero_name, &n.ctx().unit_ty()).refl(),
            )
        });
        Iso::new(
            &input_ty,
            &output_ty,
            fwd.unbind(),
            rev.unbind(),
            fwd_rev.unbind(),
            rev_fwd.unbind(),
        )
    }

    pub fn reflexive_equality_to_unit(eq_term: &Tm<S>) -> Iso<S> {
        let ctx = eq_term.ctx();
        Iso::new(
            &eq_term.equals(&eq_term),
            &ctx.unit_ty(),
            |_| ctx.unit_term(),
            |_| eq_term.refl(),
            |eq| {
                eq
                .unique_identity(
                    |eq_term, eq| eq_term.refl().equals(&eq),
                    |eq_term| eq_term.refl().refl(),
                )
            },
            |_| ctx.unit_term().refl(),
        )
    }

    pub fn uniquely_inhabited_ty_to_unit(unique_term: &Tm<S>) -> Iso<S> {
        let ctx = unique_term.ctx();
        assert_eq!(Some(unique_term.clone()), unique_term.ty().unique_term_opt());

        Iso::new(
            &unique_term.ty(),
            &ctx.unit_ty(),
            |_| ctx.unit_term(),
            |_| unique_term.clone(),
            |_| unique_term.refl(),
            |_| ctx.unit_term().refl(),
        )
    }

    /*
    // TODO: finish this
    pub fn try_for_loop_congruence(
        elim: &Tm<S>,
        zero_inhab_iso: &Iso<S>,
        succ_inhab_iso: impl FnOnce(Tm<S>, Ty<S>) -> Iso<S>,
    ) -> Option<Iso<S>> {
        same_ctx!(elim, zero_inhab_iso);

        let succ_inhab_iso = {
            elim
            .ctx()
            .nat()
            .scope(|elim| {
                elim
                .ctx()
                .universe()
                .scope(|state| {
                    same_ctx!(&elim, &state);

                    let state = state.to_ty();
                    succ_inhab_iso(elim, state)
                })
            })
        };

        let input_name = S::name_from_str("input");
        let output_name = S::name_from_str("output");

        let succ_inhab_map_input = {
            elim
            .ctx()
            .nat()
            .try_scope(|elim| {
                elim
                .ctx()
                .universe()
                .try_scope(|input_ty| {
                    let input_ty = input_ty.to_ty();

                    input_ty
                    .ctx()
                    .universe()
                    .try_scope(|output_ty| {
                        same_ctx!(&input_ty, &output_ty);
                        let output_ty = output_ty.to_ty();

                        input_ty
                        .pi(&input_name, |_| output_ty.clone())
                        .try_scope(|mapping| {
                            same_ctx!(&input_ty, &mapping, &succ_inhab_iso, &elim);
                            let mapping = input_ty.scope(|input| mapping.app(&input));

                            let succ_inhab_input_ty = {
                                succ_inhab_iso
                                .bind(&elim)
                                .map(|_, iso| iso.input_ty())
                            };
                            succ_inhab_input_ty.try_map_functor(&mapping)
                        })
                    })
                })
            })?
        };

        let succ_inhab_map_output = {
            elim
            .ctx()
            .nat()
            .try_scope(|elim| {
                elim
                .ctx()
                .universe()
                .try_scope(|input_ty| {
                    let input_ty = input_ty.to_ty();

                    input_ty
                    .ctx()
                    .universe()
                    .try_scope(|output_ty| {
                        let output_ty = output_ty.to_ty();

                        output_ty
                        .pi(&output_name, |_| input_ty.clone())
                        .try_scope(|mapping| {
                            same_ctx!(&input_ty, &mapping, &succ_inhab_iso, &elim);
                            let mapping = output_ty.scope(|output| mapping.app(&output));

                            let succ_inhab_output_ty = {
                                succ_inhab_iso
                                .bind(&elim)
                                .map(|_, iso| iso.output_ty())
                            };
                            succ_inhab_output_ty.try_map_functor(&mapping)
                        })
                    })
                })
            })?
        };

        let input_ty = {
            elim
            .ctx()
            .nat()
            .scope(|elim| {
                elim
                .for_loop(
                    |_| elim.ctx().universe(),
                    &zero_inhab_iso.input_ty().to_term(),
                    |elim, state| succ_inhab_iso.bind(&elim).bind(&state).input_ty().to_term(),
                )
                .to_ty()
            })
        };

        let output_ty = {
            elim
            .ctx()
            .nat()
            .scope(|elim| {
                elim
                .for_loop(
                    |_| elim.ctx().universe(),
                    &zero_inhab_iso.output_ty().to_term(),
                    |elim, state| succ_inhab_iso.bind(&elim).bind(&state).output_ty().to_term(),
                )
                .to_ty()
            })
        };

        let fwd = {
            elim
            .ctx()
            .nat()
            .scope(|elim| {
                elim
                .for_loop(
                    |elim| {
                        input_ty
                        .bind(&elim)
                        .pi(&input_name, |_| output_ty.bind(&elim))
                    },
                    &zero_inhab_iso
                    .input_ty()
                    .func(&input_name, |input| zero_inhab_iso.fwd(&input)),
                    |elim, state| {
                        succ_inhab_iso
                        .bind(&elim)
                        .bind(&input_ty.bind(&elim).to_term())
                        .input_ty()
                        .func(&input_name, |input| {
                            succ_inhab_iso
                            .bind(&elim)
                            .bind(&output_ty.bind(&elim).to_term())
                            .fwd(
                                &succ_inhab_map_input
                                .bind(&elim)
                                .bind(&input_ty.bind(&elim).to_term())
                                .bind(&output_ty.bind(&elim).to_term())
                                .bind(&state)
                                .bind(&input)
                            )
                        })
                    },
                )
                .to_scope()
            })
        };

        let rev = {
            elim
            .ctx()
            .nat()
            .scope(|elim| {
                elim
                .for_loop(
                    |elim| {
                        output_ty
                        .bind(&elim)
                        .pi(&output_name, |_| input_ty.bind(&elim))
                    },
                    &zero_inhab_iso
                    .output_ty()
                    .func(&output_name, |output| zero_inhab_iso.rev(&output)),
                    |elim, state| {
                        succ_inhab_iso
                        .bind(&elim)
                        .bind(&output_ty.bind(&elim).to_term())
                        .output_ty()
                        .func(&output_name, |output| {
                            succ_inhab_iso
                            .bind(&elim)
                            .bind(&input_ty.bind(&elim).to_term())
                            .rev(
                                &succ_inhab_map_output
                                .bind(&elim)
                                .bind(&input_ty.bind(&elim).to_term())
                                .bind(&output_ty.bind(&elim).to_term())
                                .bind(&state)
                                .bind(&output)
                            )
                        })
                    },
                )
                .to_scope()
            })
        };
        
        let fwd_rev = {
            elim
            .for_loop(
                |elim| {
                    input_ty
                    .bind(&elim)
                    .pi(&input_name, |input| {
                        rev.bind(&elim).bind(&fwd.bind(&elim).bind(&input)).equals(&input)
                    })
                },
                &zero_inhab_iso
                .input_ty()
                .func(&input_name, |input| {
                    zero_inhab_iso.fwd_rev(&input)
                }),
                |elim, state| {

                },
            )
        };

        todo!()
    }
    */

    pub fn cong_congruence(
        elim: &Tm<S>,
        inhab_iso: impl FnOnce(Tm<S>) -> Iso<S>,
    ) -> Iso<S> {
        let (eq_term_0, eq_term_1) = elim.ty().unwrap_equal();
        let eq_ty = eq_term_0.ty();
        let inhab_iso = eq_ty.scope(inhab_iso);

        let input_name = S::name_from_str("CongInput");
        let output_name = S::name_from_str("CongOutput");

        let input_ty = {
            eq_ty
            .scope(|eq_term_0| {
                eq_ty
                .weaken_into(&eq_term_0.ctx())
                .scope(|eq_term_1| {
                    eq_term_0
                    .equals(&eq_term_1)
                    .scope(|elim| {
                        elim
                        .cong(
                            |_, _, _| elim.ctx().universe(),
                            |val| inhab_iso.bind(&val).input_ty().to_term(),
                        )
                        .to_ty()
                    })
                })
            })
        };
        let output_ty = {
            eq_ty
            .scope(|eq_term_0| {
                eq_ty
                .weaken_into(&eq_term_0.ctx())
                .scope(|eq_term_1| {
                    eq_term_0
                    .equals(&eq_term_1)
                    .scope(|elim| {
                        elim
                        .cong(
                            |_, _, _| elim.ctx().universe(),
                            |val| inhab_iso.bind(&val).output_ty().to_term(),
                        )
                        .to_ty()
                    })
                })
            })
        };

        let fwd = {
            eq_ty
            .scope(|eq_term_0| {
                eq_ty
                .weaken_into(&eq_term_0.ctx())
                .scope(|eq_term_1| {
                    eq_term_0
                    .equals(&eq_term_1)
                    .scope(|elim| {
                        input_ty
                        .bind(&eq_term_0)
                        .bind(&eq_term_1)
                        .bind(&elim)
                        .scope(|input| {
                            elim
                            .weaken_into(&input.ctx())
                            .cong(
                                |eq_term_0, eq_term_1, elim| {
                                    input_ty
                                    .bind(&eq_term_0)
                                    .bind(&eq_term_1)
                                    .bind(&elim)
                                    .pi(&input_name, |_| {
                                        output_ty
                                        .bind(&eq_term_0)
                                        .bind(&eq_term_1)
                                        .bind(&elim)
                                    })
                                },
                                |val| {
                                    inhab_iso
                                    .bind(&val)
                                    .input_ty()
                                    .func(&input_name, |input| {
                                        inhab_iso.bind(&val).fwd(&input)
                                    })
                                },
                            )
                            .app(&input)
                        })
                    })
                })
            })
        };

        let rev = {
            eq_ty
            .scope(|eq_term_0| {
                eq_ty
                .weaken_into(&eq_term_0.ctx())
                .scope(|eq_term_1| {
                    eq_term_0
                    .equals(&eq_term_1)
                    .scope(|elim| {
                        output_ty
                        .bind(&eq_term_0)
                        .bind(&eq_term_1)
                        .bind(&elim)
                        .scope(|output| {
                            elim
                            .weaken_into(&output.ctx())
                            .cong(
                                |eq_term_0, eq_term_1, elim| {
                                    output_ty
                                    .bind(&eq_term_0)
                                    .bind(&eq_term_1)
                                    .bind(&elim)
                                    .pi(&output_name, |_| {
                                        input_ty
                                        .bind(&eq_term_0)
                                        .bind(&eq_term_1)
                                        .bind(&elim)
                                    })
                                },
                                |val| {
                                    inhab_iso
                                    .bind(&val)
                                    .output_ty()
                                    .func(&output_name, |output| {
                                        inhab_iso.bind(&val).rev(&output)
                                    })
                                },
                            )
                            .app(&output)
                        })
                    })
                })
            })
        };

        let fwd_rev = {
            input_ty
            .bind(&eq_term_0)
            .bind(&eq_term_1)
            .bind(&elim)
            .scope(|input| {
                elim
                .cong(
                    |eq_term_0, eq_term_1, elim| {
                        input_ty
                        .bind(&eq_term_0)
                        .bind(&eq_term_1)
                        .bind(&elim)
                        .pi(&input_name, |input| {
                            rev
                            .bind(&eq_term_0)
                            .bind(&eq_term_1)
                            .bind(&elim)
                            .bind(
                                &fwd
                                .bind(&eq_term_0)
                                .bind(&eq_term_1)
                                .bind(&elim)
                                .bind(&input)
                            )
                            .equals(&input)
                        })
                    },
                    |val| {
                        inhab_iso
                        .bind(&val)
                        .input_ty()
                        .func(&input_name, |input| {
                            inhab_iso
                            .bind(&val)
                            .fwd_rev(&input)
                        })
                    },
                )
                .app(&input)
            })
        };

        let rev_fwd = {
            output_ty
            .bind(&eq_term_0)
            .bind(&eq_term_1)
            .bind(&elim)
            .scope(|output| {
                elim
                .cong(
                    |eq_term_0, eq_term_1, elim| {
                        output_ty
                        .bind(&eq_term_0)
                        .bind(&eq_term_1)
                        .bind(&elim)
                        .pi(&output_name, |output| {
                            fwd
                            .bind(&eq_term_0)
                            .bind(&eq_term_1)
                            .bind(&elim)
                            .bind(
                                &rev
                                .bind(&eq_term_0)
                                .bind(&eq_term_1)
                                .bind(&elim)
                                .bind(&output)
                            )
                            .equals(&output)
                        })
                    },
                    |val| {
                        inhab_iso
                        .bind(&val)
                        .output_ty()
                        .func(&output_name, |output| {
                            inhab_iso
                            .bind(&val)
                            .rev_fwd(&output)
                        })
                    },
                )
                .app(&output)
            })
        };

        let input_ty = {
            input_ty
            .bind(&eq_term_0)
            .bind(&eq_term_1)
            .bind(&elim)
        };
        let output_ty = {
            output_ty
            .bind(&eq_term_0)
            .bind(&eq_term_1)
            .bind(&elim)
        };
        let fwd = {
            fwd
            .bind(&eq_term_0)
            .bind(&eq_term_1)
            .bind(&elim)
        };
        let rev = {
            rev
            .bind(&eq_term_0)
            .bind(&eq_term_1)
            .bind(&elim)
        };

        Iso::new(
            &input_ty,
            &output_ty,
            fwd.unbind(),
            rev.unbind(),
            fwd_rev.unbind(),
            rev_fwd.unbind(),
        )
    }

    pub fn cong_ty_lift(
        elim: &Tm<S>,
        inhab: &Ty<S>,
    ) -> Iso<S> {
        same_ctx!(elim, inhab);

        let (eq_term_0, eq_term_1) = elim.ty().unwrap_equal();
        let eq_ty = eq_term_0.ty();
        let cong_name = S::name_from_str("Cong");

        let input_ty = {
            eq_ty
            .scope(|eq_term_0| {
                same_ctx!(&eq_ty, &eq_term_0);
                eq_ty
                .scope(|eq_term_1| {
                    eq_term_0
                    .equals(&eq_term_1)
                    .scope(|elim| {
                        elim
                        .cong(
                            |_, _, _| elim.ctx().universe(),
                            |_| inhab.to_term(),
                        )
                        .to_ty()
                    })
                })
            })
        };

        let fwd = {
            eq_ty
            .scope(|eq_term_0| {
                same_ctx!(&eq_ty, &eq_term_0);
                eq_ty
                .scope(|eq_term_1| {
                    eq_term_0
                    .equals(&eq_term_1)
                    .scope(|elim| {
                        input_ty
                        .bind(&eq_term_0)
                        .bind(&eq_term_1)
                        .bind(&elim)
                        .scope(|cong| {
                            same_ctx!(&elim, &cong);

                            elim
                            .cong(
                                |eq_term_0, eq_term_1, elim| {
                                    input_ty
                                    .bind(&eq_term_0)
                                    .bind(&eq_term_1)
                                    .bind(&elim)
                                    .pi(&cong_name, |_| {
                                        inhab.clone()
                                    })
                                },
                                |_| {
                                    inhab.func(&cong_name, |cong| cong)
                                },
                            )
                            .app(&cong)
                        })
                    })
                })
            })
        };

        let rev = {
            eq_ty
            .scope(|eq_term_0| {
                same_ctx!(&eq_ty, &eq_term_0);
                eq_ty
                .scope(|eq_term_1| {
                    eq_term_0
                    .equals(&eq_term_1)
                    .scope(|elim| {
                        same_ctx!(&elim, &inhab);

                        inhab
                        .scope(|cong| {
                            same_ctx!(&elim, &cong);

                            elim
                            .cong(
                                |eq_term_0, eq_term_1, elim| {
                                    input_ty
                                    .bind(&eq_term_0)
                                    .bind(&eq_term_1)
                                    .bind(&elim)
                                },
                                |_| cong,
                            )
                        })
                    })
                })
            })
        };

        let fwd_rev = {
            input_ty
            .bind(&eq_term_0)
            .bind(&eq_term_1)
            .bind(&elim)
            .scope(|cong| {
                same_ctx!(&elim, &cong);

                elim
                .cong(
                    |eq_term_0, eq_term_1, elim| {
                        input_ty
                        .bind(&eq_term_0)
                        .bind(&eq_term_1)
                        .bind(&elim)
                        .pi(&cong_name, |cong| {
                            rev
                            .bind(&eq_term_0)
                            .bind(&eq_term_1)
                            .bind(&elim)
                            .bind(
                                &fwd
                                .bind(&eq_term_0)
                                .bind(&eq_term_1)
                                .bind(&elim)
                                .bind(&cong)
                            )
                            .equals(&cong)
                        })
                    },
                    |_| {
                        inhab
                        .func(&cong_name, |cong| cong.refl())
                    },
                )
                .app(&cong)
            })
        };

        let rev_fwd = {
            inhab
            .scope(|cong| {
                same_ctx!(&elim, &cong);

                elim
                .cong(
                    |eq_term_0, eq_term_1, elim| {
                        fwd
                        .bind(&eq_term_0)
                        .bind(&eq_term_1)
                        .bind(&elim)
                        .bind(
                            &rev
                            .bind(&eq_term_0)
                            .bind(&eq_term_1)
                            .bind(&elim)
                            .bind(&cong)
                        )
                        .equals(&cong)
                    },
                    |_| {
                        cong.refl()
                    },
                )
            })
        };

        let input_ty = input_ty.bind(&eq_term_0).bind(&eq_term_1).bind(&elim);
        let fwd = fwd.bind(&eq_term_0).bind(&eq_term_1).bind(&elim);
        let rev = rev.bind(&eq_term_0).bind(&eq_term_1).bind(&elim);

        Iso::new(
            &input_ty,
            &inhab,
            fwd.unbind(),
            rev.unbind(),
            fwd_rev.unbind(),
            rev_fwd.unbind(),
        )
    }

    pub fn unique_identity_congruence(
        elim: &Tm<S>,
        inhab_iso: impl FnOnce(Tm<S>) -> Iso<S>,
    ) -> Iso<S> {
        let (eq_term_0, eq_term_1) = elim.ty().unwrap_equal();
        let eq_term = as_equal(&eq_term_0, &eq_term_1).unwrap();
        let eq_ty = eq_term.ty();
        let inhab_iso = eq_ty.scope(inhab_iso);

        let input_name = S::name_from_str("UniqueIdentityInput");
        let output_name = S::name_from_str("UniqueIdentityOutput");

        let input_ty = {
            eq_ty
            .scope(|eq_term| {
                eq_term
                .equals(&eq_term)
                .scope(|elim| {
                    elim
                    .unique_identity(
                        |_, _| elim.ctx().universe(),
                        |val| inhab_iso.bind(&val).input_ty().to_term(),
                    )
                    .to_ty()
                })
            })
        };
        let output_ty = {
            eq_ty
            .scope(|eq_term| {
                eq_term
                .equals(&eq_term)
                .scope(|elim| {
                    elim
                    .unique_identity(
                        |_, _| elim.ctx().universe(),
                        |val| inhab_iso.bind(&val).output_ty().to_term(),
                    )
                    .to_ty()
                })
            })
        };

        let fwd = {
            eq_ty
            .scope(|eq_term| {
                eq_term
                .equals(&eq_term)
                .scope(|elim| {
                    input_ty
                    .bind(&eq_term)
                    .bind(&elim)
                    .scope(|input| {
                        elim
                        .weaken_into(&input.ctx())
                        .unique_identity(
                            |eq_term, elim| {
                                input_ty
                                .bind(&eq_term)
                                .bind(&elim)
                                .pi(&input_name, |_| {
                                    output_ty
                                    .bind(&eq_term)
                                    .bind(&elim)
                                })
                            },
                            |val| {
                                inhab_iso
                                .bind(&val)
                                .input_ty()
                                .func(&input_name, |input| {
                                    inhab_iso.bind(&val).fwd(&input)
                                })
                            },
                        )
                        .app(&input)
                    })
                })
            })
        };

        let rev = {
            eq_ty
            .scope(|eq_term| {
                eq_term
                .equals(&eq_term)
                .scope(|elim| {
                    output_ty
                    .bind(&eq_term)
                    .bind(&elim)
                    .scope(|output| {
                        elim
                        .weaken_into(&output.ctx())
                        .unique_identity(
                            |eq_term, elim| {
                                output_ty
                                .bind(&eq_term)
                                .bind(&elim)
                                .pi(&output_name, |_| {
                                    input_ty
                                    .bind(&eq_term)
                                    .bind(&elim)
                                })
                            },
                            |val| {
                                inhab_iso
                                .bind(&val)
                                .output_ty()
                                .func(&output_name, |output| {
                                    inhab_iso.bind(&val).rev(&output)
                                })
                            },
                        )
                        .app(&output)
                    })
                })
            })
        };

        let fwd_rev = {
            input_ty
            .bind(&eq_term)
            .bind(&elim)
            .scope(|input| {
                elim
                .unique_identity(
                    |eq_term, elim| {
                        input_ty
                        .bind(&eq_term)
                        .bind(&elim)
                        .pi(&input_name, |input| {
                            rev
                            .bind(&eq_term)
                            .bind(&elim)
                            .bind(
                                &fwd
                                .bind(&eq_term)
                                .bind(&elim)
                                .bind(&input)
                            )
                            .equals(&input)
                        })
                    },
                    |val| {
                        inhab_iso
                        .bind(&val)
                        .input_ty()
                        .func(&input_name, |input| {
                            inhab_iso
                            .bind(&val)
                            .fwd_rev(&input)
                        })
                    },
                )
                .app(&input)
            })
        };

        let rev_fwd = {
            output_ty
            .bind(&eq_term)
            .bind(&elim)
            .scope(|output| {
                elim
                .unique_identity(
                    |eq_term, elim| {
                        output_ty
                        .bind(&eq_term)
                        .bind(&elim)
                        .pi(&output_name, |output| {
                            fwd
                            .bind(&eq_term)
                            .bind(&elim)
                            .bind(
                                &rev
                                .bind(&eq_term)
                                .bind(&elim)
                                .bind(&output)
                            )
                            .equals(&output)
                        })
                    },
                    |val| {
                        inhab_iso
                        .bind(&val)
                        .output_ty()
                        .func(&output_name, |output| {
                            inhab_iso
                            .bind(&val)
                            .rev_fwd(&output)
                        })
                    },
                )
                .app(&output)
            })
        };

        let input_ty = {
            input_ty
            .bind(&eq_term)
            .bind(&elim)
        };
        let output_ty = {
            output_ty
            .bind(&eq_term)
            .bind(&elim)
        };
        let fwd = {
            fwd
            .bind(&eq_term)
            .bind(&elim)
        };
        let rev = {
            rev
            .bind(&eq_term)
            .bind(&elim)
        };

        Iso::new(
            &input_ty,
            &output_ty,
            fwd.unbind(),
            rev.unbind(),
            fwd_rev.unbind(),
            rev_fwd.unbind(),
        )
    }

    pub fn unique_identity_ty_lift(
        elim: &Tm<S>,
        inhab: &Ty<S>,
    ) -> Iso<S> {
        same_ctx!(elim, inhab);

        let (eq_term_0, eq_term_1) = elim.ty().unwrap_equal();
        let eq_term = as_equal(&eq_term_0, &eq_term_1).unwrap();
        let eq_ty = eq_term_0.ty();
        let unique_identity_name = S::name_from_str("UniqueIdentity");

        let input_ty = {
            eq_ty
            .scope(|eq_term| {
                eq_term
                .equals(&eq_term)
                .scope(|elim| {
                    elim
                    .unique_identity(
                        |_, _| elim.ctx().universe(),
                        |_| inhab.to_term(),
                    )
                    .to_ty()
                })
            })
        };

        let fwd = {
            eq_ty
            .scope(|eq_term| {
                eq_term
                .equals(&eq_term)
                .scope(|elim| {
                    input_ty
                    .bind(&eq_term)
                    .bind(&elim)
                    .scope(|unique_identity| {
                        same_ctx!(&elim, &unique_identity);

                        elim
                        .unique_identity(
                            |eq_term, elim| {
                                input_ty
                                .bind(&eq_term)
                                .bind(&elim)
                                .pi(&unique_identity_name, |_| {
                                    inhab.clone()
                                })
                            },
                            |_| {
                                inhab
                                .func(&unique_identity_name, |unique_identity| unique_identity)
                            },
                        )
                        .app(&unique_identity)
                    })
                })
            })
        };

        let rev = {
            eq_ty
            .scope(|eq_term| {
                eq_term
                .equals(&eq_term)
                .scope(|elim| {
                    same_ctx!(&elim, &inhab);

                    inhab
                    .scope(|unique_identity| {
                        same_ctx!(&elim, &unique_identity);

                        elim
                        .unique_identity(
                            |eq_term, elim| {
                                input_ty
                                .bind(&eq_term)
                                .bind(&elim)
                            },
                            |_| unique_identity,
                        )
                    })
                })
            })
        };

        let fwd_rev = {
            input_ty
            .bind(&eq_term)
            .bind(&elim)
            .scope(|unique_identity| {
                same_ctx!(&elim, &unique_identity);

                elim
                .unique_identity(
                    |eq_term, elim| {
                        input_ty
                        .bind(&eq_term)
                        .bind(&elim)
                        .pi(&unique_identity_name, |unique_identity| {
                            rev
                            .bind(&eq_term)
                            .bind(&elim)
                            .bind(
                                &fwd
                                .bind(&eq_term)
                                .bind(&elim)
                                .bind(&unique_identity)
                            )
                            .equals(&unique_identity)
                        })
                    },
                    |_| {
                        inhab
                        .func(&unique_identity_name, |unique_identity| unique_identity.refl())
                    },
                )
                .app(&unique_identity)
            })
        };

        let rev_fwd = {
            inhab
            .scope(|unique_identity| {
                same_ctx!(&elim, &unique_identity);

                elim
                .unique_identity(
                    |eq_term, elim| {
                        fwd
                        .bind(&eq_term)
                        .bind(&elim)
                        .bind(
                            &rev
                            .bind(&eq_term)
                            .bind(&elim)
                            .bind(&unique_identity)
                        )
                        .equals(&unique_identity)
                    },
                    |_| {
                        unique_identity.refl()
                    },
                )
            })
        };

        let input_ty = input_ty.bind(&eq_term).bind(&elim);
        let fwd = fwd.bind(&eq_term).bind(&elim);
        let rev = rev.bind(&eq_term).bind(&elim);

        Iso::new(
            &input_ty,
            &inhab,
            fwd.unbind(),
            rev.unbind(),
            fwd_rev.unbind(),
            rev_fwd.unbind(),
        )
    }

    pub fn case_congruence(
        elim: &Tm<S>,
        lhs_inhab_iso: impl FnOnce(Tm<S>) -> Iso<S>,
        rhs_inhab_iso: impl FnOnce(Tm<S>) -> Iso<S>,
    ) -> Iso<S> {
        let (lhs_name, lhs_ty, rhs_ty) = elim.ty().unwrap_sum();
        let lhs_inhab_iso = lhs_ty.scope(lhs_inhab_iso);
        let rhs_inhab_iso = rhs_ty.scope(rhs_inhab_iso);

        let case_val_name = S::name_from_str("case_val");

        let input_ty = {
            elim
            .ty()
            .scope(|elim| {
                elim
                .case(
                    |_| elim.ctx().universe(),
                    |lhs| {
                        lhs_inhab_iso
                        .bind(&lhs)
                        .input_ty()
                        .to_term()
                    },
                    |rhs| {
                        rhs_inhab_iso
                        .bind(&rhs)
                        .input_ty()
                        .to_term()
                    },
                )
                .to_ty()
            })
        };

        let output_ty = {
            elim
            .ty()
            .scope(|elim| {
                elim
                .case(
                    |_| elim.ctx().universe(),
                    |lhs| {
                        lhs_inhab_iso
                        .bind(&lhs)
                        .output_ty()
                        .to_term()
                    },
                    |rhs| {
                        rhs_inhab_iso
                        .bind(&rhs)
                        .output_ty()
                        .to_term()
                    },
                )
                .to_ty()
            })
        };

        let fwd = {
            elim
            .ty()
            .scope(|elim| {
                input_ty
                .bind(&elim)
                .scope(|case_val| {
                    elim
                    .case(
                        |elim| {
                            input_ty
                            .bind(&elim)
                            .pi(&case_val_name, |_| {
                                output_ty.bind(&elim)
                            })
                        },
                        |lhs| {
                            input_ty
                            .bind(&lhs.inj_lhs(&lhs_name, &rhs_ty))
                            .func(&case_val_name, |case_val| {
                                lhs_inhab_iso.bind(&lhs).fwd(&case_val)
                            })
                        },
                        |rhs| {
                            input_ty
                            .bind(&rhs.inj_rhs(&lhs_name, &lhs_ty))
                            .func(&case_val_name, |case_val| {
                                rhs_inhab_iso.bind(&rhs).fwd(&case_val)
                            })
                        },
                    )
                    .app(&case_val)
                })
            })
        };

        let rev = {
            elim
            .ty()
            .scope(|elim| {
                output_ty
                .bind(&elim)
                .scope(|case_val| {
                    elim
                    .case(
                        |elim| {
                            output_ty
                            .bind(&elim)
                            .pi(&case_val_name, |_| {
                                input_ty.bind(&elim)
                            })
                        },
                        |lhs| {
                            output_ty
                            .bind(&lhs.inj_lhs(&lhs_name, &rhs_ty))
                            .func(&case_val_name, |case_val| {
                                lhs_inhab_iso.bind(&lhs).rev(&case_val)
                            })
                        },
                        |rhs| {
                            output_ty
                            .bind(&rhs.inj_rhs(&lhs_name, &lhs_ty))
                            .func(&case_val_name, |case_val| {
                                rhs_inhab_iso.bind(&rhs).rev(&case_val)
                            })
                        },
                    )
                    .app(&case_val)
                })
            })
        };

        let fwd_rev = {
            input_ty
            .bind(&elim)
            .scope(|case_val| {
                elim
                .case(
                    |elim| {
                        input_ty
                        .bind(&elim)
                        .pi(&case_val_name, |case_val| {
                            rev
                            .bind(&elim)
                            .bind(&fwd.bind(&elim).bind(&case_val))
                            .equals(&case_val)
                        })
                    },
                    |lhs| {
                        input_ty
                        .bind(&lhs.inj_lhs(&lhs_name, &rhs_ty))
                        .func(&case_val_name, |case_val| {
                            lhs_inhab_iso.bind(&lhs).fwd_rev(&case_val)
                        })
                    },
                    |rhs| {
                        input_ty
                        .bind(&rhs.inj_rhs(&lhs_name, &lhs_ty))
                        .func(&case_val_name, |case_val| {
                            rhs_inhab_iso.bind(&rhs).fwd_rev(&case_val)
                        })
                    },
                )
                .app(&case_val)
            })
        };

        let rev_fwd = {
            output_ty
            .bind(&elim)
            .scope(|case_val| {
                elim
                .case(
                    |elim| {
                        output_ty
                        .bind(&elim)
                        .pi(&case_val_name, |case_val| {
                            fwd
                            .bind(&elim)
                            .bind(&rev.bind(&elim).bind(&case_val))
                            .equals(&case_val)
                        })
                    },
                    |lhs| {
                        output_ty
                        .bind(&lhs.inj_lhs(&lhs_name, &rhs_ty))
                        .func(&case_val_name, |case_val| {
                            lhs_inhab_iso.bind(&lhs).rev_fwd(&case_val)
                        })
                    },
                    |rhs| {
                        output_ty
                        .bind(&rhs.inj_rhs(&lhs_name, &lhs_ty))
                        .func(&case_val_name, |case_val| {
                            rhs_inhab_iso.bind(&rhs).rev_fwd(&case_val)
                        })
                    },
                )
                .app(&case_val)
            })
        };

        let input_ty = input_ty.bind(&elim);
        let output_ty = output_ty.bind(&elim);
        let fwd = fwd.bind(&elim);
        let rev = rev.bind(&elim);

        Iso::new(
            &input_ty,
            &output_ty,
            fwd.unbind(),
            rev.unbind(),
            fwd_rev.unbind(),
            rev_fwd.unbind(),
        )
    }

    pub fn case_ty_lift(
        elim: &Tm<S>,
        inhab: &Ty<S>,
    ) -> Iso<S> {
        same_ctx!(elim, inhab);

        let case_val_name = S::name_from_str("case_val");

        let input_ty = {
            elim
            .ty()
            .scope(|elim| {
                elim
                .case(
                    |_| elim.ctx().universe(),
                    |_| inhab.to_term(),
                    |_| inhab.to_term(),
                )
                .to_ty()
            })
        };

        let fwd = {
            elim
            .ty()
            .scope(|elim| {
                input_ty
                .bind(&elim)
                .scope(|case_val| {
                    same_ctx!(&elim, &case_val);

                    elim
                    .case(
                        |elim| {
                            input_ty
                            .bind(&elim)
                            .pi(&case_val_name, |_| {
                                inhab.clone()
                            })
                        },
                        |_| inhab.func(&case_val_name, |case_val| case_val),
                        |_| inhab.func(&case_val_name, |case_val| case_val),
                    )
                    .app(&case_val)
                })
            })
        };

        let rev = {
            elim
            .ty()
            .scope(|elim| {
                same_ctx!(&elim, &inhab);

                inhab
                .scope(|case_val| {
                    same_ctx!(&elim, &case_val);

                    elim
                    .case(
                        |elim| input_ty.bind(&elim),
                        |_| case_val.clone(),
                        |_| case_val.clone(),
                    )
                })
            })
        };
        
        let fwd_rev = {
            input_ty
            .bind(&elim)
            .scope(|case_val| {
                same_ctx!(&elim, &case_val);

                elim
                .case(
                    |elim| {
                        input_ty
                        .bind(&elim)
                        .pi(&case_val_name, |case_val| {
                            rev
                            .bind(&elim)
                            .bind(&fwd.bind(&elim).bind(&case_val))
                            .equals(&case_val)
                        })
                    },
                    |_| inhab.func(&case_val_name, |case_val| case_val.refl()),
                    |_| inhab.func(&case_val_name, |case_val| case_val.refl()),
                )
                .app(&case_val)
            })
        };

        let rev_fwd = {
            inhab
            .scope(|case_val| {
                same_ctx!(&elim, &case_val);

                elim
                .case(
                    |elim| {
                        fwd
                        .bind(&elim)
                        .bind(&rev.bind(&elim).bind(&case_val))
                        .equals(&case_val)
                    },
                    |_| case_val.refl(),
                    |_| case_val.refl(),
                )
            })
        };

        let input_ty = input_ty.bind(&elim);
        let fwd = fwd.bind(&elim);
        let rev = rev.bind(&elim);

        Iso::new(
            &input_ty,
            &inhab,
            fwd.unbind(),
            rev.unbind(),
            fwd_rev.unbind(),
            rev_fwd.unbind(),
        )
    }

    pub fn function_extensionality(
        arg_name: &Name<S>,
        arg_ty: &Ty<S>,
        pointwise_eq: impl FnOnce(Tm<S>) -> Ty<S>,
        funext: &Tm<S>,
    ) -> Iso<S> {
        same_ctx!(arg_name, arg_ty, funext);
        let pointwise_eq = arg_ty.scope(pointwise_eq);

        let (func_0, func_1) = pointwise_eq.map_out(|_, ty| {
            ty.unwrap_equal()
        });
        let func_0 = Scope::new(func_0);
        let func_1 = Scope::new(func_1);

        let input_ty = pointwise_eq.to_pi(&arg_name);
        let output_ty = {
            func_0
            .to_func(&arg_name)
            .equals(&func_1.to_func(&arg_name))
        };

        let fwd = input_ty.scope(|pointwise_eq| {
            pointwise_eq.apply_funext(&funext)
        });

        let rev = output_ty.scope(|func_eq| {
            arg_ty
            .weaken_into(&func_eq.ctx())
            .func(&arg_name, |arg| {
                func_eq
                .weaken_into(&arg.ctx())
                .map_eq(|func| func.app(&arg))
            })
        });

        let fwd_rev = input_ty.scope(|pointwise_eq| {
            arg_ty
            .weaken_into(&pointwise_eq.ctx())
            .func(&arg_name, |arg| {
                pointwise_eq
                .weaken_into(&arg.ctx())
                .apply_funext(&funext)
                .map_eq(|func| func.app(&arg))
                .equality_contractible(
                    &pointwise_eq.app(&arg)
                )
            })
            .apply_funext(&funext)
        });

        let rev_fwd = output_ty.scope(|func_eq| {
            fwd
            .bind(&rev.bind(&func_eq))
            .equality_contractible(&func_eq)
        });

        Iso::new(
            &input_ty,
            &output_ty,
            fwd.unbind(),
            rev.unbind(),
            fwd_rev.unbind(),
            rev_fwd.unbind(),
        )
    }
}

