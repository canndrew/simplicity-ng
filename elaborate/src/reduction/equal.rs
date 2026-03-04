use crate::priv_prelude::*;

impl InferScope<Tm> {
    pub(crate) fn reduce_constraint_equality(&self, recursion_depth: u32) -> Reduction {
        let constraint_name = self.constraint_name();
        let constraint_ty = self.constraint_ty();
        let _body = self.body();
        let (eq_term_0, eq_term_1) = constraint_ty.unwrap_equal();

        if let Some(eq_term) = as_equal(&eq_term_0, &eq_term_1) {
            return self.reduce_over_iso(
                &Iso::reflexive_equality_to_unit(eq_term),
                &constraint_name,
            );
        }

        match (eq_term_0.kind(), eq_term_1.kind()) {
            (TmKind::Tag { tag: tag_0 }, TmKind::Tag { tag: tag_1 }) => {
                debug_assert_ne!(tag_0, tag_1);
                return self.reduce_impossible(|eq| {
                    eq.tags_apart()
                });
            },

            (TmKind::Type { ty: ty_0 }, TmKind::Type { ty: ty_1 }) => {
                match (ty_0.kind(), ty_1.kind()) {
                    (TyKind::Equal { .. }, TyKind::Equal { .. }) => {
                        return self.reduce_equal_equality_tys().reduce_more(recursion_depth);
                    },
                    (TyKind::Sum { .. }, TyKind::Sum { .. }) => {
                        return self.reduce_equal_sum_tys().reduce_more(recursion_depth);
                    },
                    (TyKind::Sigma { .. }, TyKind::Sigma { .. }) => {
                        return self.reduce_equal_sigma_tys().reduce_more(recursion_depth);
                    },
                    (TyKind::Pi { .. }, TyKind::Pi { .. }) => {
                        return self.reduce_equal_pi_tys().reduce_more(recursion_depth);
                    },

                    _ => (),
                }

                if let Some(uninhabited_0) = ty_0.try_prove_uninhabited() {
                    if let Some(term_1) = ty_1.try_find_arbitrary_term() {
                        return self.reduce_impossible(|eq| {
                            uninhabited_0
                            .contradiction(
                                &eq.symmetry().transport(&term_1),
                            )
                        });
                    }
                }
                if let Some(uninhabited_1) = ty_1.try_prove_uninhabited() {
                    if let Some(term_0) = ty_0.try_find_arbitrary_term() {
                        return self.reduce_impossible(|eq| {
                            uninhabited_1
                            .contradiction(
                                &eq.transport(&term_0),
                            )
                        });
                    }
                }
            },

            (
                TmKind::InjLhs { lhs_name, lhs_term: lhs_term_0, rhs_ty },
                TmKind::InjLhs { lhs_term: lhs_term_1, .. },
            ) => {
                return self.reduce_equality(
                    &lhs_term_0.equals(&lhs_term_1),
                    |lhs_eq| lhs_eq.map_eq(|lhs| lhs.inj_lhs(&lhs_name, &rhs_ty)),
                    |eq| eq.case_eq(),
                );
            },
            (
                TmKind::InjRhs { lhs_name, rhs_term: rhs_term_0, lhs_ty },
                TmKind::InjRhs { rhs_term: rhs_term_1, .. },
            ) => {
                return {
                    self
                    .reduce_equality(
                        &rhs_term_0.equals(&rhs_term_1),
                        |rhs_eq| rhs_eq.map_eq(|rhs| rhs.inj_rhs(&lhs_name, &lhs_ty)),
                        |eq| eq.case_eq(),
                    )
                    .reduce_more(recursion_depth)
                };
            },
            (TmKind::InjLhs { .. }, TmKind::InjRhs { .. }) |
            (TmKind::InjRhs { .. }, TmKind::InjLhs { .. }) => {
                return self.reduce_equality(
                    &self.ctx().never(),
                    |never| never.explode(|_| constraint_ty),
                    |eq| eq.case_eq(),
                );
            },

            (TmKind::Pair { .. }, TmKind::Pair { .. }) => {
                return self.reduce_equality_of_pairs().reduce_more(recursion_depth);
            },

            _ => (),
        }

        self.irreducible()
    }

    pub(crate) fn reduce_equality(
        &self,
        new_constraint_ty: &Ty,
        fwd: impl FnOnce(Tm) -> Tm,
        rev: impl FnOnce(Tm) -> Tm,
    ) -> Reduction {
        let constraint_ty = self.constraint_ty();
        let constraint_name = self.constraint_name();

        let fwd = new_constraint_ty.scope(fwd);
        let rev = constraint_ty.scope(rev);

        let body = self.body();
        let body_ty = body.map(|_, term| term.ty());
        let new_constraint_ty = fwd.var_ty();

        let covering_ty = constraint_ty.scope(|eq| {
            body_ty
            .bind_eq(&eq.equality_contractible(&fwd.bind(&rev.bind(&eq))))
        });
        let covering = constraint_ty.scope(|eq| {
            eq
            .equality_contractible(&fwd.bind(&rev.bind(&eq)))
            .cong(
                |eq_0, eq_1, eq_eq| {
                    body_ty
                    .bind_eq(&eq_eq)
                    .heterogeneous_equal(
                        &body.bind(&eq_0),
                        &body.bind(&eq_1),
                    )
                },
                |eq| body.bind(&eq).refl()
            )
        });

        Reduction::new(
            &constraint_name,
            &constraint_name,
            &body,
            &new_constraint_ty,
            fwd.unbind(),
            rev.unbind(),
            covering_ty.unbind(),
            covering.unbind(),
        )
    }

    pub(crate) fn reduce_equality_of_pairs(&self) -> Reduction {
        let (eq_term_0, eq_term_1) = self.constraint_ty().unwrap_equal();
        let TmKind::Pair {
            head_name,
            tail_ty,
            head_term: head_term_0,
            tail_term: tail_term_0,
        } = eq_term_0.kind() else { panic!() };
        let TmKind::Pair {
            head_name: head_name_1,
            tail_ty: tail_ty_1,
            head_term: head_term_1,
            tail_term: tail_term_1,
        } = eq_term_1.kind() else { panic!() };

        debug_assert_eq!(head_name, head_name_1);
        debug_assert_eq!(tail_ty, tail_ty_1);

        self.reduce_equality(
            &head_term_0
            .equals(&head_term_1)
            .sigma(&head_name, |head_eq| {
                tail_ty
                .bind_eq(&head_eq)
                .heterogeneous_equal(&tail_term_0, &tail_term_1)
            }),
            |eq_pair| {
                eq_pair
                .proj_head()
                .pair_eq(
                    &head_name,
                    tail_ty.unbind(),
                    &tail_term_0,
                    &tail_term_1,
                    &eq_pair.proj_tail(),
                )
            },
            |pair_eq| {
                pair_eq
                .cong(
                    |pair_0, pair_1, _| {
                        pair_0
                        .proj_head()
                        .equals(&pair_1.proj_head())
                        .sigma(&head_name, |head_eq| {
                            tail_ty
                            .bind_eq(&head_eq)
                            .heterogeneous_equal(
                                &pair_0.proj_tail(),
                                &pair_1.proj_tail(),
                            )
                        })
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
            },
        )
    }

    pub(crate) fn reduce_equal_equality_tys(&self) -> Reduction {
        let constraint_ty = self.constraint_ty();
        let (eq_term_0, eq_term_1) = constraint_ty.unwrap_equal();
        let ty_0 = eq_term_0.to_ty();
        let ty_1 = eq_term_1.to_ty();
        let (eq_term_0_0, eq_term_1_0) = ty_0.unwrap_equal();
        let (eq_term_0_1, eq_term_1_1) = ty_1.unwrap_equal();
        let eq_ty_0 = eq_term_0_0.ty();
        let eq_ty_1 = eq_term_0_1.ty();

        let ty_eq_name = TagScheme::name_from_str("ty_eq");
        let val_0_eq_name = TagScheme::name_from_str("val_0_eq");
        let val_1_eq_name = TagScheme::name_from_str("val_1_eq");

        let val_0_0_name = TagScheme::name_from_str("val_0_0");
        let val_1_0_name = TagScheme::name_from_str("val_0_0");
        let val_0_1_name = TagScheme::name_from_str("val_0_1");
        let val_1_1_name = TagScheme::name_from_str("val_0_1");
        let eq_ty_eq_name = TagScheme::name_from_str("eq_ty_eq");
        let endpoints_eq_name = TagScheme::name_from_str("endpoints_eq");

        let eq_ty_equal_ty = {
            eq_ty_0
            .to_term()
            .equals(&eq_ty_1.to_term())
        };

        let generic_new_constraint_tail_ty = {
            self
            .ctx()
            .universe()
            .scope(|eq_ty_0| {
                let eq_ty_0 = eq_ty_0.to_ty();

                eq_ty_0
                .ctx()
                .universe()
                .scope(|eq_ty_1| {
                    let eq_ty_1 = eq_ty_1.to_ty();

                    eq_ty_0
                    .to_term()
                    .equals(&eq_ty_1.to_term())
                    .scope(|eq_ty_equal| {
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
                    })
                })
            })
        };

        let new_constraint_tail_ty = eq_ty_equal_ty.scope(|eq_ty_equal| {
            generic_new_constraint_tail_ty
            .bind(&eq_ty_0.to_term())
            .bind(&eq_ty_1.to_term())
            .bind(&eq_ty_equal)
            .app(&eq_term_0_0)
            .app(&eq_term_1_0)
            .app(&eq_term_0_1)
            .app(&eq_term_1_1)
            .to_ty()
        });

        let new_constraint_ty = new_constraint_tail_ty.to_sigma(&ty_eq_name);

        let fwd = new_constraint_ty.scope(|components_eq| {
            let eq_ty_equal = components_eq.proj_head();
            let endpoints_eq = components_eq.proj_tail();

            eq_ty_equal
            .cong(
                |eq_ty_0, eq_ty_1, eq_ty_equal| {
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
                                    generic_new_constraint_tail_ty
                                    .weaken_into(&eq_term_1_1.ctx())
                                    .bind(&eq_ty_0.to_term())
                                    .bind(&eq_ty_1.to_term())
                                    .bind(&eq_ty_equal)
                                    .app(&eq_term_0_0)
                                    .app(&eq_term_1_0)
                                    .app(&eq_term_0_1)
                                    .app(&eq_term_1_1)
                                    .to_ty()
                                    .pi(&endpoints_eq_name, |_endpoints_eq| {
                                        eq_term_0_0
                                        .equals(&eq_term_1_0)
                                        .to_term()
                                        .equals(
                                            &eq_term_0_1
                                            .equals(&eq_term_1_1)
                                            .to_term()
                                        )
                                    })
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
                                    .func(&endpoints_eq_name, |endpoints_eq| {
                                        endpoints_eq
                                        .proj_head()
                                        .cong(
                                            |eq_term_0_0, eq_term_0_1, _| {
                                                eq_term_0_0
                                                .equals(&eq_term_1_0)
                                                .to_term()
                                                .equals(
                                                    &eq_term_0_1
                                                    .equals(&eq_term_1_1)
                                                    .to_term()
                                                )
                                            },
                                            |eq_term_0| {
                                                endpoints_eq
                                                .proj_tail()
                                                .proj_head()
                                                .weaken_into(&eq_term_0.ctx())
                                                .cong(
                                                    |eq_term_1_0, eq_term_1_1, _| {
                                                        eq_term_0
                                                        .equals(&eq_term_1_0)
                                                        .to_term()
                                                        .equals(
                                                            &eq_term_0
                                                            .equals(&eq_term_1_1)
                                                            .to_term()
                                                        )
                                                    },
                                                    |eq_term_1| {
                                                        eq_term_0
                                                        .equals(&eq_term_1)
                                                        .to_term()
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
            .app(&endpoints_eq)
        });

        let rev = constraint_ty.scope(|eq| {
            let eq_ty_equal = eq.equal_eq_eq_ty_injective();

            eq_ty_equal
            .pair(
                &ty_eq_name,
                new_constraint_tail_ty.unbind(),
                &eq_ty_equal
                .cong(
                    |eq_ty_0, eq_ty_1, eq_ty_equal| {
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
                                        eq_term_0_0
                                        .equals(&eq_term_1_0)
                                        .to_term()
                                        .equals(
                                            &eq_term_0_1
                                            .equals(&eq_term_1_1)
                                            .to_term()
                                        )
                                        .pi(&eq_ty_eq_name, |eq| {
                                            generic_new_constraint_tail_ty
                                            .weaken_into(&eq.ctx())
                                            .bind(&eq_ty_0.to_term())
                                            .bind(&eq_ty_1.to_term())
                                            .bind(&eq_ty_equal)
                                            .app(&eq_term_0_0)
                                            .app(&eq_term_1_0)
                                            .app(&eq_term_0_1)
                                            .app(&eq_term_1_1)
                                            .to_ty()
                                        })
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
                                        .equals(&eq_term_1_0)
                                        .to_term()
                                        .equals(
                                            &eq_term_0_1
                                            .equals(&eq_term_1_1)
                                            .to_term()
                                        )
                                        .func(&eq_ty_eq_name, |eq| {
                                            eq
                                            .equal_eq_eq_term_0_injective()
                                            .pair(
                                                &val_0_eq_name,
                                                |_| {
                                                    eq_term_1_0
                                                    .equals(&eq_term_1_1)
                                                    .sigma(&val_1_eq_name, |val_1_eq| {
                                                        val_1_eq.ctx().unit_ty()
                                                    })
                                                },
                                                &eq
                                                .equal_eq_eq_term_1_injective()
                                                .pair(
                                                    &val_1_eq_name,
                                                    |_| eq.ctx().unit_ty(),
                                                    &eq.ctx().unit_term(),
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
                .app(&eq)
            )
        });

        self.reduce_equality(
            &new_constraint_ty,
            fwd.unbind(),
            rev.unbind(),
        )
    }

    pub(crate) fn reduce_equal_sum_tys(&self) -> Reduction {
        let constraint_ty = self.constraint_ty();
        let (eq_term_0, eq_term_1) = constraint_ty.unwrap_equal();
        let ty_0 = eq_term_0.to_ty();
        let ty_1 = eq_term_1.to_ty();
        let (lhs_name_0, lhs_ty_0, rhs_ty_0) = ty_0.unwrap_sum();
        let (lhs_name_1, lhs_ty_1, rhs_ty_1) = ty_1.unwrap_sum();

        let lhs_name_eq_name = TagScheme::name_from_str("lhs_name_eq");
        let lhs_ty_eq_name = TagScheme::name_from_str("lhs_ty_eq");
        let rhs_ty_eq_name = TagScheme::name_from_str("rhs_ty_eq");

        let new_constraint_ty = {
            lhs_name_0
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
                    .sigma(&rhs_ty_eq_name, |_| {
                        self.ctx().unit_ty()
                    })
                })
            })
        };
        
        let fwd = new_constraint_ty.scope(|components_eq| {
            let lhs_name_eq = components_eq.proj_head();
            let lhs_ty_eq = components_eq.proj_tail().proj_head();
            let rhs_ty_eq = components_eq.proj_tail().proj_tail().proj_head();
            Tm::map_eqs(
                [&lhs_name_eq, &lhs_ty_eq, &rhs_ty_eq],
                |[lhs_name, lhs_ty, rhs_ty]| {
                    lhs_ty.to_ty().sum(&lhs_name.to_name(), &rhs_ty.to_ty()).to_term()
                },
            )
        });
        let rev = constraint_ty.scope(|sum_ty_eq| {
            sum_ty_eq
            .sum_eq_name_injective()
            .pair(
                &lhs_name_eq_name,
                |_| {
                    lhs_ty_0
                    .to_term()
                    .equals(&lhs_ty_1.to_term())
                    .sigma(&lhs_ty_eq_name, |_| {
                        rhs_ty_0
                        .to_term()
                        .equals(&rhs_ty_1.to_term())
                        .sigma(&rhs_ty_eq_name, |_| {
                            self.ctx().unit_ty()
                        })
                    })
                },
                &sum_ty_eq
                .sum_eq_lhs_injective()
                .pair(
                    &lhs_ty_eq_name,
                    |_| {
                        rhs_ty_0
                        .to_term()
                        .equals(&rhs_ty_1.to_term())
                        .sigma(&rhs_ty_eq_name, |_| {
                            self.ctx().unit_ty()
                        })
                    },
                    &sum_ty_eq
                    .sum_eq_rhs_injective()
                    .pair(
                        &rhs_ty_eq_name,
                        |_| self.ctx().unit_ty(),
                        &self.ctx().unit_term(),
                    )
                )
            )
        });

        self.reduce_equality(
            &new_constraint_ty,
            fwd.unbind(),
            rev.unbind(),
        )
    }

    fn reduce_equal_sigma_tys(&self) -> Reduction {
        let constraint_name = self.constraint_name();
        let constraint_ty = self.constraint_ty();
        let (eq_term_0, eq_term_1) = constraint_ty.unwrap_equal();
        let ty_0 = eq_term_0.to_ty();
        let ty_1 = eq_term_1.to_ty();
        let (head_name_0, tail_ty_0) = ty_0.unwrap_sigma();
        let (head_name_1, tail_ty_1) = ty_1.unwrap_sigma();
        let head_ty_0 = tail_ty_0.var_ty();
        let head_ty_1 = tail_ty_1.var_ty();

        let head_name_eq_name = TagScheme::name_from_str("head_name_eq");
        let head_ty_eq_name = TagScheme::name_from_str("head_ty_eq");
        let tail_ty_eq_name = TagScheme::name_from_str("tail_ty_eq");

        let tail_ty_0_name = TagScheme::name_from_str("tail_ty_0");
        let tail_ty_1_name = TagScheme::name_from_str("tail_ty_1");

        let generic_tail_ty_eq_ty = {
            self
            .ctx()
            .name()
            .scope(|head_name_0| {
                let head_name_0 = head_name_0.to_name();
                head_name_0
                .ctx()
                .name()
                .scope(|head_name_1| {
                    let head_name_1 = head_name_1.to_name();

                    head_name_0
                    .to_term()
                    .equals(&head_name_1.to_term())
                    .scope(|head_name_eq| {
                        head_name_eq
                        .ctx()
                        .universe()
                        .scope(|head_ty_0| {
                            let head_ty_0 = head_ty_0.to_ty();
                            head_ty_0
                            .ctx()
                            .universe()
                            .scope(|head_ty_1| {
                                let head_ty_1 = head_ty_1.to_ty();

                                head_ty_0
                                .to_term()
                                .equals(&head_ty_1.to_term())
                                .scope(|head_ty_eq| {
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
                                })
                            })
                        })
                    })
                })
            })
        };

        let new_constraint_ty = {
            head_name_0
            .to_term()
            .equals(&head_name_1.to_term())
            .sigma(&head_name_eq_name, |head_name_eq| {
                head_ty_0
                .to_term()
                .equals(&head_ty_1.to_term())
                .weaken_into(&head_name_eq.ctx())
                .sigma(&head_ty_eq_name, |head_ty_eq| {
                    generic_tail_ty_eq_ty
                    .bind(&head_name_0.to_term())
                    .bind(&head_name_1.to_term())
                    .bind(&head_name_eq)
                    .bind(&head_ty_0.to_term())
                    .bind(&head_ty_1.to_term())
                    .bind(&head_ty_eq)
                    .app(&head_ty_0.func(&head_name_0, |head| tail_ty_0.bind(&head).to_term()))
                    .app(&head_ty_1.func(&head_name_1, |head| tail_ty_1.bind(&head).to_term()))
                    .to_ty()
                })
            })
        };

        let fwd = new_constraint_ty.scope(|components_eq| {
            let head_name_eq = components_eq.proj_head();
            let head_ty_eq = components_eq.proj_tail().proj_head();
            let tail_ty_eq = components_eq.proj_tail().proj_tail();

            head_name_eq
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
                            generic_tail_ty_eq_ty
                            .weaken_into(&tail_ty_1.ctx())
                            .bind(&head_name_0.to_term())
                            .bind(&head_name_1.to_term())
                            .bind(&head_name_eq)
                            .bind(&head_ty_0.to_term())
                            .bind(&head_ty_1.to_term())
                            .bind(&head_ty_eq)
                            .app(&tail_ty_0)
                            .app(&tail_ty_1)
                            .to_ty()
                            .pi(&tail_ty_eq_name, |_| {
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
                            })
                        })
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
                                    generic_tail_ty_eq_ty
                                    .weaken_into(&tail_ty_1.ctx())
                                    .bind(&head_name.to_term())
                                    .bind(&head_name.to_term())
                                    .bind(&head_name.to_term().refl())
                                    .bind(&head_ty_0.to_term())
                                    .bind(&head_ty_1.to_term())
                                    .bind(&head_ty_eq)
                                    .app(&tail_ty_0)
                                    .app(&tail_ty_1)
                                    .to_ty()
                                    .pi(&tail_ty_eq_name, |_| {
                                        head_ty_0
                                        .weaken_into(&tail_ty_1.ctx())
                                        .sigma(&head_name, |head| {
                                            tail_ty_0.app(&head).to_ty()
                                        })
                                        .to_term()
                                        .equals(
                                            &head_ty_1
                                            .weaken_into(&tail_ty_1.ctx())
                                            .sigma(&head_name, |head| {
                                                tail_ty_1.app(&head).to_ty()
                                            })
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
                                            .sigma(&head_name, |head| {
                                                tail_ty.app(&head).to_ty()
                                            })
                                            .to_term()
                                        })
                                    })
                                })
                            })
                        },
                    )
                },
            )
            .app(&head_ty_0.func(&head_name_0, |head| tail_ty_0.bind(&head).to_term()))
            .app(&head_ty_1.func(&head_name_1, |head| tail_ty_1.bind(&head).to_term()))
            .app(&tail_ty_eq)
        });

        let rev = constraint_ty.scope(|sigma_ty_eq| {
            sigma_ty_eq
            .sigma_eq_name_injective()
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
                            .pi(&constraint_name, |sigma_ty_eq| {
                                head_name_0
                                .to_term()
                                .equals(&head_name_1.to_term())
                                .weaken_into(&sigma_ty_eq.ctx())
                                .sigma(&head_name_eq_name, |head_name_eq| {
                                    let head_ty_0 = head_ty_0.weaken_into(&head_name_eq.ctx());
                                    let head_ty_1 = head_ty_1.weaken_into(&head_name_eq.ctx());

                                    head_ty_0
                                    .to_term()
                                    .equals(&head_ty_1.to_term())
                                    .sigma(&head_ty_eq_name, |head_ty_eq| {
                                        generic_tail_ty_eq_ty
                                        .bind(&head_name_0.to_term())
                                        .bind(&head_name_1.to_term())
                                        .bind(&head_name_eq)
                                        .bind(&head_ty_0.to_term())
                                        .bind(&head_ty_1.to_term())
                                        .bind(&head_ty_eq)
                                        .app(&head_ty_0.func(&head_name_0, |head| {
                                            tail_ty_0.app(&head)
                                        }))
                                        .app(&head_ty_1.func(&head_name_1, |head| {
                                            tail_ty_1.app(&head)
                                        }))
                                        .to_ty()
                                    })
                                })
                            })
                        })
                    })
                },
                |head_name| {
                    let head_name = head_name.to_name();

                    sigma_ty_eq
                    .sigma_eq_head_injective()
                    .weaken_into(&head_name.ctx())
                    .cong(
                        |head_ty_0, head_ty_1, _| {
                            let head_ty_0 = head_ty_0.to_ty();
                            let head_ty_1 = head_ty_1.to_ty();

                            head_ty_0
                            .pi(&head_name, |head| head.ctx().universe())
                            .pi(&tail_ty_0_name, |tail_ty_0| {
                                head_ty_1
                                .weaken_into(&tail_ty_0.ctx())
                                .pi(&head_name, |head| head.ctx().universe())
                                .pi(&tail_ty_1_name, |tail_ty_1| {
                                    head_ty_0
                                    .weaken_into(&tail_ty_1.ctx())
                                    .sigma(&head_name, |head| {
                                        tail_ty_0.app(&head).to_ty()
                                    })
                                    .to_term()
                                    .equals(
                                        &head_ty_1
                                        .weaken_into(&tail_ty_1.ctx())
                                        .sigma(&head_name, |head| {
                                            tail_ty_1.app(&head).to_ty()
                                        })
                                        .to_term()
                                    )
                                    .pi(&constraint_name, |sigma_ty_eq| {
                                        head_name
                                        .to_term()
                                        .equals(&head_name.to_term())
                                        .weaken_into(&sigma_ty_eq.ctx())
                                        .sigma(&head_name_eq_name, |head_name_eq| {
                                            let head_ty_0 = head_ty_0.weaken_into(
                                                &head_name_eq.ctx(),
                                            );
                                            let head_ty_1 = head_ty_1.weaken_into(
                                                &head_name_eq.ctx(),
                                            );

                                            head_ty_0
                                            .to_term()
                                            .equals(&head_ty_1.to_term())
                                            .weaken_into(&head_name_eq.ctx())
                                            .sigma(&head_ty_eq_name, |head_ty_eq| {
                                                generic_tail_ty_eq_ty
                                                .bind(&head_name.to_term())
                                                .bind(&head_name.to_term())
                                                .bind(&head_name_eq)
                                                .bind(&head_ty_0.to_term())
                                                .bind(&head_ty_1.to_term())
                                                .bind(&head_ty_eq)
                                                .app(&head_ty_0.func(&head_name, |head| {
                                                    tail_ty_0.app(&head)
                                                }))
                                                .app(&head_ty_1.func(&head_name, |head| {
                                                    tail_ty_1.app(&head)
                                                }))
                                                .to_ty()
                                            })
                                        })
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
                                    head_ty
                                    .weaken_into(&tail_ty_1.ctx())
                                    .sigma(&head_name, |head| {
                                        tail_ty_0.app(&head).to_ty()
                                    })
                                    .to_term()
                                    .equals(
                                        &head_ty
                                        .weaken_into(&tail_ty_1.ctx())
                                        .sigma(&head_name, |head| {
                                            tail_ty_1.app(&head).to_ty()
                                        })
                                        .to_term()
                                    )
                                    .func(&constraint_name, |sigma_ty_eq| {
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
                                                    let head_ty = head_ty.weaken_into(
                                                        &head_ty_eq.ctx()
                                                    );
                                                    generic_tail_ty_eq_ty
                                                    .bind(&head_name.to_term())
                                                    .bind(&head_name.to_term())
                                                    .bind(&head_name_eq)
                                                    .bind(&head_ty.to_term())
                                                    .bind(&head_ty.to_term())
                                                    .bind(&head_ty_eq)
                                                    .app(&head_ty.func(&head_name, |head| {
                                                        tail_ty_0.app(&head)
                                                    }))
                                                    .app(&head_ty.func(&head_name, |head| {
                                                        tail_ty_1.app(&head)
                                                    }))
                                                    .to_ty()
                                                })
                                            },
                                            &head_ty
                                            .to_term()
                                            .refl()
                                            .pair(
                                                &head_ty_eq_name,
                                                |head_ty_eq| {
                                                    let head_ty = head_ty.weaken_into(
                                                        &head_ty_eq.ctx()
                                                    );
                                                    generic_tail_ty_eq_ty
                                                    .bind(&head_name.to_term())
                                                    .bind(&head_name.to_term())
                                                    .bind(&head_name.to_term().refl())
                                                    .bind(&head_ty.to_term())
                                                    .bind(&head_ty.to_term())
                                                    .bind(&head_ty_eq)
                                                    .app(&head_ty.func(&head_name, |head| {
                                                        tail_ty_0.app(&head)
                                                    }))
                                                    .app(&head_ty.func(&head_name, |head| {
                                                        tail_ty_1.app(&head)
                                                    }))
                                                    .to_ty()
                                                },
                                                &sigma_ty_eq
                                                .sigma_eq_tail_injective(),
                                            )
                                        )
                                    })
                                })
                            })
                        },
                    )
                },
            )
            .app(&head_ty_0.func(&head_name_0, |head| tail_ty_0.bind(&head).to_term()))
            .app(&head_ty_1.func(&head_name_1, |head| tail_ty_1.bind(&head).to_term()))
            .app(&sigma_ty_eq)
        });

        self.reduce_equality(
            &new_constraint_ty,
            fwd.unbind(),
            rev.unbind(),
        )
    }

    fn reduce_equal_pi_tys(&self) -> Reduction {
        let constraint_name = self.constraint_name();
        let constraint_ty = self.constraint_ty();
        let (eq_term_0, eq_term_1) = constraint_ty.unwrap_equal();
        let ty_0 = eq_term_0.to_ty();
        let ty_1 = eq_term_1.to_ty();
        let (arg_name_0, res_ty_0) = ty_0.unwrap_pi();
        let (arg_name_1, res_ty_1) = ty_1.unwrap_pi();
        let arg_ty_0 = res_ty_0.var_ty();
        let arg_ty_1 = res_ty_1.var_ty();

        let arg_name_eq_name = TagScheme::name_from_str("arg_name_eq");
        let arg_ty_eq_name = TagScheme::name_from_str("arg_ty_eq");
        let res_ty_eq_name = TagScheme::name_from_str("res_ty_eq");

        let res_ty_0_name = TagScheme::name_from_str("res_ty_0");
        let res_ty_1_name = TagScheme::name_from_str("res_ty_1");

        let generic_res_ty_eq_ty = {
            self
            .ctx()
            .name()
            .scope(|arg_name_0| {
                let arg_name_0 = arg_name_0.to_name();
                arg_name_0
                .ctx()
                .name()
                .scope(|arg_name_1| {
                    let arg_name_1 = arg_name_1.to_name();

                    arg_name_0
                    .to_term()
                    .equals(&arg_name_1.to_term())
                    .scope(|arg_name_eq| {
                        arg_name_eq
                        .ctx()
                        .universe()
                        .scope(|arg_ty_0| {
                            let arg_ty_0 = arg_ty_0.to_ty();
                            arg_ty_0
                            .ctx()
                            .universe()
                            .scope(|arg_ty_1| {
                                let arg_ty_1 = arg_ty_1.to_ty();

                                arg_ty_0
                                .to_term()
                                .equals(&arg_ty_1.to_term())
                                .scope(|arg_ty_eq| {
                                    arg_name_eq
                                    .weaken_into(&arg_ty_eq.ctx())
                                    .cong(
                                        |arg_name_0, arg_name_1, arg_name_eq| {
                                            let arg_name_0 = arg_name_0.to_name();
                                            let arg_name_1 = arg_name_1.to_name();

                                            arg_ty_0
                                            .weaken_into(&arg_name_eq.ctx())
                                            .pi(&arg_name_0, |arg| arg.ctx().universe())
                                            .pi(&res_ty_0_name, |res_ty_0| {
                                                arg_ty_1
                                                .weaken_into(&res_ty_0.ctx())
                                                .pi(&arg_name_1, |arg| arg.ctx().universe())
                                                .pi(&res_ty_1_name, |res_ty_1| {
                                                    res_ty_1.ctx().universe()
                                                })
                                            })
                                        },
                                        |arg_name| {
                                            let arg_name = arg_name.to_name();

                                            arg_ty_eq
                                            .weaken_into(&arg_name.ctx())
                                            .cong(
                                                |arg_ty_0, arg_ty_1, _| {
                                                    let arg_ty_0 = arg_ty_0.to_ty();
                                                    let arg_ty_1 = arg_ty_1.to_ty();

                                                    arg_ty_0
                                                    .pi(&arg_name, |arg| {
                                                        arg.ctx().universe()
                                                    })
                                                    .pi(&res_ty_0_name, |res_ty_0| {
                                                        arg_ty_1
                                                        .weaken_into(&res_ty_0.ctx())
                                                        .pi(&arg_name, |arg| {
                                                            arg.ctx().universe()
                                                        })
                                                        .pi(&res_ty_1_name, |res_ty_1| {
                                                            res_ty_1.ctx().universe()
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
                                                        .pi(&arg_name, |arg| {
                                                            arg.ctx().universe()
                                                        })
                                                        .func(&res_ty_1_name, |res_ty_1| {
                                                            res_ty_0.equals(&res_ty_1).to_term()
                                                        })
                                                    })
                                                },
                                            )
                                        },
                                    )
                                })
                            })
                        })
                    })
                })
            })
        };

        let new_constraint_ty = {
            arg_name_0
            .to_term()
            .equals(&arg_name_1.to_term())
            .sigma(&arg_name_eq_name, |arg_name_eq| {
                arg_ty_0
                .to_term()
                .equals(&arg_ty_1.to_term())
                .weaken_into(&arg_name_eq.ctx())
                .sigma(&arg_ty_eq_name, |arg_ty_eq| {
                    generic_res_ty_eq_ty
                    .bind(&arg_name_0.to_term())
                    .bind(&arg_name_1.to_term())
                    .bind(&arg_name_eq)
                    .bind(&arg_ty_0.to_term())
                    .bind(&arg_ty_1.to_term())
                    .bind(&arg_ty_eq)
                    .app(&arg_ty_0.func(&arg_name_0, |arg| res_ty_0.bind(&arg).to_term()))
                    .app(&arg_ty_1.func(&arg_name_1, |arg| res_ty_1.bind(&arg).to_term()))
                    .to_ty()
                })
            })
        };

        let fwd = new_constraint_ty.scope(|components_eq| {
            let arg_name_eq = components_eq.proj_head();
            let arg_ty_eq = components_eq.proj_tail().proj_head();
            let res_ty_eq = components_eq.proj_tail().proj_tail();

            arg_name_eq
            .cong(
                |arg_name_0, arg_name_1, arg_name_eq| {
                    let arg_name_0 = arg_name_0.to_name();
                    let arg_name_1 = arg_name_1.to_name();

                    arg_ty_0
                    .weaken_into(&arg_name_eq.ctx())
                    .pi(&arg_name_0, |arg| arg.ctx().universe())
                    .pi(&res_ty_0_name, |res_ty_0| {
                        arg_ty_1
                        .weaken_into(&res_ty_0.ctx())
                        .pi(&arg_name_1, |arg| arg.ctx().universe())
                        .pi(&res_ty_1_name, |res_ty_1| {
                            generic_res_ty_eq_ty
                            .weaken_into(&res_ty_1.ctx())
                            .bind(&arg_name_0.to_term())
                            .bind(&arg_name_1.to_term())
                            .bind(&arg_name_eq)
                            .bind(&arg_ty_0.to_term())
                            .bind(&arg_ty_1.to_term())
                            .bind(&arg_ty_eq)
                            .app(&res_ty_0)
                            .app(&res_ty_1)
                            .to_ty()
                            .pi(&res_ty_eq_name, |_| {
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
                            })
                        })
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
                                    generic_res_ty_eq_ty
                                    .weaken_into(&res_ty_1.ctx())
                                    .bind(&arg_name.to_term())
                                    .bind(&arg_name.to_term())
                                    .bind(&arg_name.to_term().refl())
                                    .bind(&arg_ty_0.to_term())
                                    .bind(&arg_ty_1.to_term())
                                    .bind(&arg_ty_eq)
                                    .app(&res_ty_0)
                                    .app(&res_ty_1)
                                    .to_ty()
                                    .pi(&res_ty_eq_name, |_| {
                                        arg_ty_0
                                        .weaken_into(&res_ty_1.ctx())
                                        .pi(&arg_name, |arg| {
                                            res_ty_0.app(&arg).to_ty()
                                        })
                                        .to_term()
                                        .equals(
                                            &arg_ty_1
                                            .weaken_into(&res_ty_1.ctx())
                                            .pi(&arg_name, |arg| {
                                                res_ty_1.app(&arg).to_ty()
                                            })
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
                                            .pi(&arg_name, |arg| {
                                                res_ty.app(&arg).to_ty()
                                            })
                                            .to_term()
                                        })
                                    })
                                })
                            })
                        },
                    )
                },
            )
            .app(&arg_ty_0.func(&arg_name_0, |arg| res_ty_0.bind(&arg).to_term()))
            .app(&arg_ty_1.func(&arg_name_1, |arg| res_ty_1.bind(&arg).to_term()))
            .app(&res_ty_eq)
        });

        let rev = constraint_ty.scope(|pi_ty_eq| {
            pi_ty_eq
            .pi_eq_name_injective()
            .cong(
                |arg_name_0, arg_name_1, arg_name_eq| {
                    let arg_name_0 = arg_name_0.to_name();
                    let arg_name_1 = arg_name_1.to_name();

                    arg_ty_0
                    .weaken_into(&arg_name_eq.ctx())
                    .pi(&arg_name_0, |arg| arg.ctx().universe())
                    .pi(&res_ty_0_name, |res_ty_0| {
                        arg_ty_1
                        .weaken_into(&res_ty_0.ctx())
                        .pi(&arg_name_1, |arg| arg.ctx().universe())
                        .pi(&res_ty_1_name, |res_ty_1| {
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
                            .pi(&constraint_name, |pi_ty_eq| {
                                arg_name_0
                                .to_term()
                                .equals(&arg_name_1.to_term())
                                .weaken_into(&pi_ty_eq.ctx())
                                .sigma(&arg_name_eq_name, |arg_name_eq| {
                                    let arg_ty_0 = arg_ty_0.weaken_into(&arg_name_eq.ctx());
                                    let arg_ty_1 = arg_ty_1.weaken_into(&arg_name_eq.ctx());

                                    arg_ty_0
                                    .to_term()
                                    .equals(&arg_ty_1.to_term())
                                    .sigma(&arg_ty_eq_name, |arg_ty_eq| {
                                        generic_res_ty_eq_ty
                                        .bind(&arg_name_0.to_term())
                                        .bind(&arg_name_1.to_term())
                                        .bind(&arg_name_eq)
                                        .bind(&arg_ty_0.to_term())
                                        .bind(&arg_ty_1.to_term())
                                        .bind(&arg_ty_eq)
                                        .app(&arg_ty_0.func(&arg_name_0, |arg| {
                                            res_ty_0.app(&arg)
                                        }))
                                        .app(&arg_ty_1.func(&arg_name_1, |arg| {
                                            res_ty_1.app(&arg)
                                        }))
                                        .to_ty()
                                    })
                                })
                            })
                        })
                    })
                },
                |arg_name| {
                    let arg_name = arg_name.to_name();

                    pi_ty_eq
                    .pi_eq_arg_injective()
                    .weaken_into(&arg_name.ctx())
                    .cong(
                        |arg_ty_0, arg_ty_1, _| {
                            let arg_ty_0 = arg_ty_0.to_ty();
                            let arg_ty_1 = arg_ty_1.to_ty();

                            arg_ty_0
                            .pi(&arg_name, |arg| arg.ctx().universe())
                            .pi(&res_ty_0_name, |res_ty_0| {
                                arg_ty_1
                                .weaken_into(&res_ty_0.ctx())
                                .pi(&arg_name, |arg| arg.ctx().universe())
                                .pi(&res_ty_1_name, |res_ty_1| {
                                    arg_ty_0
                                    .weaken_into(&res_ty_1.ctx())
                                    .pi(&arg_name, |arg| {
                                        res_ty_0.app(&arg).to_ty()
                                    })
                                    .to_term()
                                    .equals(
                                        &arg_ty_1
                                        .weaken_into(&res_ty_1.ctx())
                                        .pi(&arg_name, |arg| {
                                            res_ty_1.app(&arg).to_ty()
                                        })
                                        .to_term()
                                    )
                                    .pi(&constraint_name, |pi_ty_eq| {
                                        arg_name
                                        .to_term()
                                        .equals(&arg_name.to_term())
                                        .weaken_into(&pi_ty_eq.ctx())
                                        .sigma(&arg_name_eq_name, |arg_name_eq| {
                                            let arg_ty_0 = arg_ty_0.weaken_into(
                                                &arg_name_eq.ctx(),
                                            );
                                            let arg_ty_1 = arg_ty_1.weaken_into(
                                                &arg_name_eq.ctx(),
                                            );

                                            arg_ty_0
                                            .to_term()
                                            .equals(&arg_ty_1.to_term())
                                            .weaken_into(&arg_name_eq.ctx())
                                            .sigma(&arg_ty_eq_name, |arg_ty_eq| {
                                                generic_res_ty_eq_ty
                                                .bind(&arg_name.to_term())
                                                .bind(&arg_name.to_term())
                                                .bind(&arg_name_eq)
                                                .bind(&arg_ty_0.to_term())
                                                .bind(&arg_ty_1.to_term())
                                                .bind(&arg_ty_eq)
                                                .app(&arg_ty_0.func(&arg_name, |arg| {
                                                    res_ty_0.app(&arg)
                                                }))
                                                .app(&arg_ty_1.func(&arg_name, |arg| {
                                                    res_ty_1.app(&arg)
                                                }))
                                                .to_ty()
                                            })
                                        })
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
                                    arg_ty
                                    .weaken_into(&res_ty_1.ctx())
                                    .pi(&arg_name, |arg| {
                                        res_ty_0.app(&arg).to_ty()
                                    })
                                    .to_term()
                                    .equals(
                                        &arg_ty
                                        .weaken_into(&res_ty_1.ctx())
                                        .pi(&arg_name, |arg| {
                                            res_ty_1.app(&arg).to_ty()
                                        })
                                        .to_term()
                                    )
                                    .func(&constraint_name, |pi_ty_eq| {
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
                                                    let arg_ty = arg_ty.weaken_into(
                                                        &arg_ty_eq.ctx()
                                                    );
                                                    generic_res_ty_eq_ty
                                                    .bind(&arg_name.to_term())
                                                    .bind(&arg_name.to_term())
                                                    .bind(&arg_name_eq)
                                                    .bind(&arg_ty.to_term())
                                                    .bind(&arg_ty.to_term())
                                                    .bind(&arg_ty_eq)
                                                    .app(&arg_ty.func(&arg_name, |arg| {
                                                        res_ty_0.app(&arg)
                                                    }))
                                                    .app(&arg_ty.func(&arg_name, |arg| {
                                                        res_ty_1.app(&arg)
                                                    }))
                                                    .to_ty()
                                                })
                                            },
                                            &arg_ty
                                            .to_term()
                                            .refl()
                                            .pair(
                                                &arg_ty_eq_name,
                                                |arg_ty_eq| {
                                                    let arg_ty = arg_ty.weaken_into(
                                                        &arg_ty_eq.ctx()
                                                    );
                                                    generic_res_ty_eq_ty
                                                    .bind(&arg_name.to_term())
                                                    .bind(&arg_name.to_term())
                                                    .bind(&arg_name.to_term().refl())
                                                    .bind(&arg_ty.to_term())
                                                    .bind(&arg_ty.to_term())
                                                    .bind(&arg_ty_eq)
                                                    .app(&arg_ty.func(&arg_name, |arg| {
                                                        res_ty_0.app(&arg)
                                                    }))
                                                    .app(&arg_ty.func(&arg_name, |arg| {
                                                        res_ty_1.app(&arg)
                                                    }))
                                                    .to_ty()
                                                },
                                                &pi_ty_eq
                                                .pi_eq_res_injective(),
                                            )
                                        )
                                    })
                                })
                            })
                        },
                    )
                },
            )
            .app(&arg_ty_0.func(&arg_name_0, |arg| res_ty_0.bind(&arg).to_term()))
            .app(&arg_ty_1.func(&arg_name_1, |arg| res_ty_1.bind(&arg).to_term()))
            .app(&pi_ty_eq)
        });

        self.reduce_equality(
            &new_constraint_ty,
            fwd.unbind(),
            rev.unbind(),
        )
    }
}

