use crate::priv_prelude::*;

#[extension(pub(crate) trait ScopeReductionEqual)]
impl Scope<Tm> {
    fn reduce_constraint_equality(&self, recursion_depth: u32) -> Reduction {
        let (eq_term_0, eq_term_1) = self.var_ty().unwrap_equal();

        if eq_term_0 == eq_term_1 {
            return self.reduce_reflexive_equality();
        }
        
        match (eq_term_0.kind(), eq_term_1.kind()) {
            (TmKind::Stuck { stuck }, _)
            if let StuckKind::StripTag { tag, elim: _ } = stuck.kind() => {
                let reduction = self.reduce_equality_tagged(&tag);
                return reduction.reduce_more(recursion_depth);
            }

            (_, TmKind::Stuck { stuck })
            if let StuckKind::StripTag { tag, elim: _ } = stuck.kind() => {
                let reduction = self.reduce_equality_tagged(&tag);
                return reduction.reduce_more(recursion_depth);
            }

            (TmKind::Type { ty: ty_0 }, TmKind::Type { ty: ty_1 }) => {
                match (ty_0.kind(), ty_1.kind()) {
                    (TyKind::Equal { .. }, TyKind::Equal { .. }) => {
                        let reduction = self.reduce_equal_type_equality();
                        return reduction.reduce_more(recursion_depth);
                    },
                    (TyKind::Sum { .. }, TyKind::Sum { .. }) => {
                        let reduction = self.reduce_sum_type_equality();
                        return reduction.reduce_more(recursion_depth);
                    },
                    (TyKind::Sigma { .. }, TyKind::Sigma { .. }) => {
                        let reduction = self.reduce_sigma_type_equality();
                        return reduction.reduce_more(recursion_depth);
                    },
                    (TyKind::Pi { .. }, TyKind::Pi { .. }) => {
                        let reduction = self.reduce_pi_type_equality();
                        return reduction.reduce_more(recursion_depth);
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

            (TmKind::Zero, TmKind::Succs { .. }) |
            (TmKind::Succs { .. }, TmKind::Zero) => {
                return self.reduce_impossible(|eq| eq.nat_eq());
            },

            (
                TmKind::Succs { count: count_0, pred_term: _ },
                TmKind::Succs { count: count_1, pred_term: _ },
            ) => {
                let count = cmp::min(count_0, count_1);
                let reduction = self.reduce_equality_to_equivprovable_constraint(
                    |eq| eq.map_eq(|nat| nat.succs(count.clone())),
                    |eq| eq.nat_succs_injective(count.clone()),
                );
                return reduction.reduce_more(recursion_depth);
            },

            (
                TmKind::InjLhs { lhs_term: _, rhs_ty },
                TmKind::InjLhs { lhs_term: _, rhs_ty: _ },
            ) => {
                let reduction = self.reduce_equality_to_equivprovable_constraint(
                    |eq| eq.map_eq(|lhs_term| lhs_term.inj_lhs(&rhs_ty)),
                    |eq| eq.case_eq(),
                );
                return reduction.reduce_more(recursion_depth);
            },

            (
                TmKind::InjRhs { lhs_ty, rhs_term: _ },
                TmKind::InjRhs { lhs_ty: _, rhs_term: _ },
            ) => {
                let reduction = self.reduce_equality_to_equivprovable_constraint(
                    |eq| eq.map_eq(|rhs_term| rhs_term.inj_rhs(&lhs_ty)),
                    |eq| eq.case_eq(),
                );
                return reduction.reduce_more(recursion_depth);
            },

            (TmKind::InjLhs { .. }, TmKind::InjRhs { .. }) |
            (TmKind::InjRhs { .. }, TmKind::InjLhs { .. }) => {
                return self.reduce_impossible(|eq| eq.case_eq());
            },

            (TmKind::Pair { tail_ty, .. }, TmKind::Pair { .. }) => {
                let reduction = if tail_ty.var_used() {
                    self.reduce_dependent_pair_equality()
                } else {
                    self.reduce_non_dependent_pair_equality()
                };
                return reduction.reduce_more(recursion_depth);
            },

            _ => (),
        }

        self.irreducible()
    }

    fn reduce_equality_to_equivprovable_constraint(
        &self,
        fwd: impl FnOnce(Tm) -> Tm,
        rev: impl FnOnce(Tm) -> Tm,
    ) -> Reduction {
        let rev = self.var_ty().scope(rev);
        let new_var_ty = rev.map(|_, rev| rev.ty()).try_strengthen().unwrap();
        let fwd = new_var_ty.scope(fwd);

        let covering_ty = self.var_ty().scope(|eq| {
            self
            .map(|_, term| term.ty())
            .bind_eq(&eq.equality_contractible(&fwd.bind(&rev.bind(&eq))))
        });
        let covering = self.var_ty().scope(|eq| {
            eq
            .equality_contractible(&fwd.bind(&rev.bind(&eq)))
            .cong(
                |eq_0, eq_1, eq_eq| {
                    self
                    .map(|_, term| term.ty())
                    .bind_eq(&eq_eq)
                    .heterogeneous_equal(
                        &self.bind(&eq_0),
                        &self.bind(&eq_1),
                    )
                },
                |eq| self.bind(&eq).refl()
            )
        });
        
        self.reduction(
            &new_var_ty,
            fwd.unbind(),
            rev.unbind(),
            covering_ty.unbind(),
            covering.unbind(),
        )
    }

    fn reduce_reflexive_equality(&self) -> Reduction {
        let (eq_term_0, eq_term_1) = self.var_ty().unwrap_equal();
        let Some(eq_term) = as_equal(eq_term_0, eq_term_1) else {
            panic!("not scoped over a reflexive equality");
        };

        let covering_ty = self.var_ty().scope(|eq| {
            self
            .map(|_, term| term.ty())
            .bind_eq(&eq.equals_refl())
        });
        let covering = self.var_ty().scope(|eq| {
            eq
            .equals_refl()
            .cong(
                |eq_0, eq_1, eq_eq| {
                    self
                    .map(|_, term| term.ty())
                    .bind_eq(&eq_eq)
                    .heterogeneous_equal(
                        &self.bind(&eq_0),
                        &self.bind(&eq_1),
                    )
                },
                |eq| {
                    self.bind(&eq).refl()
                },
            )
        });

        self.reduce_unique(
            &eq_term.refl(),
            covering_ty.unbind(),
            covering.unbind(),
        )
    }

    fn reduce_equality_tagged(&self, tag: &Tag) -> Reduction {
        let (eq_term_0, eq_term_1) = self.var_ty().unwrap_equal();

        let new_var_ty = {
            eq_term_0
            .tag(tag)
            .equals(&eq_term_1.tag(tag))
        };
        let fwd = new_var_ty.scope(|tagged_term_eq| {
            tagged_term_eq
            .map_eq(|tagged_term| tagged_term.strip_tag())
        });
        let rev = self.var_ty().scope(|term_eq| {
            term_eq
            .map_eq(|term| term.tag(tag))
        });

        self.reduce_equality_to_equivprovable_constraint(fwd.unbind(), rev.unbind())
    }

    fn reduce_equal_type_equality(&self) -> Reduction {
        let (eq_term_0, eq_term_1) = self.var_ty().unwrap_equal();
        let (eq_term_0_0, eq_term_1_0) = eq_term_0.to_ty().unwrap_equal();
        let (eq_term_0_1, eq_term_1_1) = eq_term_1.to_ty().unwrap_equal();

        let eq_ty_0 = eq_term_0_0.ty();
        let eq_ty_1 = eq_term_0_1.ty();

        let new_var_ty = {
            eq_ty_0
            .to_term()
            .equals(&eq_ty_1.to_term())
            .sigma(|eq_ty_eq| {
                eq_ty_eq
                .heterogeneous_equal(&eq_term_0_0, &eq_term_0_1)
                .sigma(|_| {
                    eq_ty_eq
                    .heterogeneous_equal(&eq_term_1_0, &eq_term_1_1)
                })
            })
        };

        let fwd = new_var_ty.scope(|equalities| {
            equalities
            .proj_head()
            .cong(
                |eq_ty_0, eq_ty_1, eq_ty_eq| {
                    let eq_ty_0 = eq_ty_0.to_ty();
                    let eq_ty_1 = eq_ty_1.to_ty();

                    eq_ty_0
                    .pi(|eq_term_0_0| {
                        eq_ty_0
                        .weaken_into(&eq_term_0_0.ctx())
                        .pi(|eq_term_1_0| {
                            eq_ty_1
                            .weaken_into(&eq_term_1_0.ctx())
                            .pi(|eq_term_0_1| {
                                eq_ty_1
                                .weaken_into(&eq_term_0_1.ctx())
                                .pi(|eq_term_1_1| {
                                    eq_ty_eq
                                    .weaken_into(&eq_term_1_1.ctx())
                                    .heterogeneous_equal(&eq_term_0_0, &eq_term_0_1)
                                    .pi(|eq_term_0_eq| {
                                        eq_ty_eq
                                        .weaken_into(&eq_term_0_eq.ctx())
                                        .heterogeneous_equal(&eq_term_1_0, &eq_term_1_1)
                                        .pi(|_| {
                                            eq_term_0_0
                                            .equals(&eq_term_1_0)
                                            .to_term()
                                            .equals(
                                                &eq_term_0_1
                                                .equals(&eq_term_1_1)
                                                .to_term(),
                                            )
                                        })
                                    })
                                })
                            })
                        })
                    })
                },
                |eq_ty| {
                    let eq_ty = eq_ty.to_ty();
                    eq_ty
                    .func(|eq_term_0_0| {
                        eq_ty
                        .weaken_into(&eq_term_0_0.ctx())
                        .func(|eq_term_1_0| {
                            eq_ty
                            .weaken_into(&eq_term_1_0.ctx())
                            .func(|eq_term_0_1| {
                                eq_ty
                                .weaken_into(&eq_term_0_1.ctx())
                                .func(|eq_term_1_1| {
                                    eq_term_0_0
                                    .equals(&eq_term_0_1)
                                    .weaken_into(&eq_term_1_1.ctx())
                                    .func(|eq_term_0_eq| {
                                        eq_term_1_0
                                        .equals(&eq_term_1_1)
                                        .weaken_into(&eq_term_0_eq.ctx())
                                        .func(|eq_term_1_eq| {
                                            eq_term_0_eq
                                            .weaken_into(&eq_term_1_eq.ctx())
                                            .cong(
                                                |eq_term_0_0, eq_term_0_1, _| {
                                                    eq_term_0_0
                                                    .equals(&eq_term_1_0)
                                                    .to_term()
                                                    .equals(
                                                        &eq_term_0_1
                                                        .equals(&eq_term_1_1)
                                                        .to_term(),
                                                    )
                                                },
                                                |eq_term_0| {
                                                    eq_term_1_eq
                                                    .weaken_into(&eq_term_0.ctx())
                                                    .map_eq(|eq_term_1| {
                                                        eq_term_0
                                                        .equals(&eq_term_1)
                                                        .to_term()
                                                    })
                                                },
                                            )
                                        })
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
            .app(&equalities.proj_tail().proj_head())
            .app(&equalities.proj_tail().proj_tail())
        });

        let rev = self.var_ty().scope(|eq| {
            eq
            .equal_eq_eq_ty_injective()
            .pair(
                |eq_ty_eq| {
                    eq_ty_eq
                    .heterogeneous_equal(&eq_term_0_0, &eq_term_0_1)
                    .sigma(|_| {
                        eq_ty_eq
                        .heterogeneous_equal(&eq_term_1_0, &eq_term_1_1)
                    })
                },
                &eq
                .equal_eq_eq_term_0_injective()
                .pair(
                    |_| {
                        eq
                        .equal_eq_eq_ty_injective()
                        .heterogeneous_equal(&eq_term_1_0, &eq_term_1_1)
                    },
                    &eq
                    .equal_eq_eq_term_1_injective(),
                ),
            )
        });

        self.reduce_equality_to_equivprovable_constraint(fwd.unbind(), rev.unbind())
    }

    fn reduce_sum_type_equality(&self) -> Reduction {
        let (eq_term_0, eq_term_1) = self.var_ty().unwrap_equal();
        let (lhs_ty_0, rhs_ty_0) = eq_term_0.to_ty().unwrap_sum();
        let (lhs_ty_1, rhs_ty_1) = eq_term_1.to_ty().unwrap_sum();

        let new_var_ty = {
            lhs_ty_0
            .to_term()
            .equals(&lhs_ty_1.to_term())
            .sigma(|_| {
                rhs_ty_0
                .to_term()
                .equals(&rhs_ty_1.to_term())
            })
        };
        let fwd = new_var_ty.scope(|pair| {
            pair
            .proj_head()
            .cong(
                |lhs_ty_0, lhs_ty_1, _| {
                    Ty::sum(&lhs_ty_0.to_ty(), &rhs_ty_0)
                    .to_term()
                    .equals(&Ty::sum(&lhs_ty_1.to_ty(), &rhs_ty_1).to_term())
                },
                |lhs_ty| {
                    pair
                    .weaken_into(&lhs_ty.ctx())
                    .proj_tail()
                    .map_eq(|rhs_ty| Ty::sum(&lhs_ty.to_ty(), &rhs_ty.to_ty()).to_term())
                },
            )
        });
        let rev = self.var_ty().scope(|eq| {
            eq
            .sum_eq_lhs_injective()
            .pair(
                |_| rhs_ty_0.to_term().equals(&rhs_ty_1.to_term()),
                &eq.sum_eq_rhs_injective(),
            )
        });

        self.reduce_equality_to_equivprovable_constraint(fwd.unbind(), rev.unbind())
    }

    fn reduce_sigma_type_equality(&self) -> Reduction {
        let (eq_term_0, eq_term_1) = self.var_ty().unwrap_equal();
        let tail_ty_0 = eq_term_0.to_ty().unwrap_sigma();
        let tail_ty_1 = eq_term_1.to_ty().unwrap_sigma();

        let new_var_ty = {
            tail_ty_0
            .var_ty()
            .to_term()
            .equals(&tail_ty_1.var_ty().to_term())
            .sigma(|head_tys_eq| {
                head_tys_eq
                .scoped_tys_equal(tail_ty_0.unbind(), tail_ty_1.unbind())
            })
        };

        let fwd = new_var_ty.scope(|pair| {
            pair
            .proj_head()
            .cong(
                |head_ty_0, head_ty_1, head_tys_eq| {
                    let head_ty_0 = head_ty_0.to_ty();
                    let head_ty_1 = head_ty_1.to_ty();

                    head_ty_0
                    .pi(|head_0| head_0.ctx().universe())
                    .pi(|tail_ty_0| {
                        let tail_ty_0 = {
                            head_ty_0
                            .weaken_into(&tail_ty_0.ctx())
                            .scope(|head| tail_ty_0.app(&head).to_ty())
                        };

                        head_ty_1
                        .weaken_into(&tail_ty_0.ctx())
                        .pi(|head_1| head_1.ctx().universe())
                        .pi(|tail_ty_1| {
                            let tail_ty_1 = {
                                head_ty_1
                                .weaken_into(&tail_ty_1.ctx())
                                .scope(|head| tail_ty_1.app(&head).to_ty())
                            };

                            head_tys_eq
                            .weaken_into(&tail_ty_1.ctx())
                            .scoped_tys_equal(tail_ty_0.unbind(), tail_ty_1.unbind())
                            .pi(|tail_tys_eq| {
                                head_ty_0
                                .weaken_into(&tail_tys_eq.ctx())
                                .sigma(tail_ty_0.unbind())
                                .to_term()
                                .equals(
                                    &head_ty_1
                                    .weaken_into(&tail_tys_eq.ctx())
                                    .sigma(tail_ty_1.unbind())
                                    .to_term()
                                )
                            })
                        })
                    })
                },
                |head_ty| {
                    let head_ty = head_ty.to_ty();

                    head_ty
                    .pi(|head| head.ctx().universe())
                    .func(|tail_ty_0| {
                        head_ty
                        .weaken_into(&tail_ty_0.ctx())
                        .pi(|head| head.ctx().universe())
                        .func(|tail_ty_1| {
                            tail_ty_0
                            .equals(&tail_ty_1)
                            .func(|tail_tys_eq| {
                                tail_tys_eq
                                .map_eq(|tail_ty| {
                                    head_ty
                                    .weaken_into(&tail_ty.ctx())
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
            .app(&pair.proj_tail())
        });

        let rev = self.var_ty().scope(|eq| {
            eq
            .sigma_eq_head_injective()
            .pair(
                |head_tys_eq| head_tys_eq.scoped_tys_equal(tail_ty_0.unbind(), tail_ty_1.unbind()),
                &eq.sigma_eq_tail_injective(),
            )
        });

        self.reduce_equality_to_equivprovable_constraint(fwd.unbind(), rev.unbind())
    }

    fn reduce_pi_type_equality(&self) -> Reduction {
        let (eq_term_0, eq_term_1) = self.var_ty().unwrap_equal();
        let res_ty_0 = eq_term_0.to_ty().unwrap_pi();
        let res_ty_1 = eq_term_1.to_ty().unwrap_pi();

        let new_var_ty = {
            res_ty_0
            .var_ty()
            .to_term()
            .equals(&res_ty_1.var_ty().to_term())
            .sigma(|arg_tys_eq| {
                arg_tys_eq
                .scoped_tys_equal(res_ty_0.unbind(), res_ty_1.unbind())
            })
        };

        let fwd = new_var_ty.scope(|pair| {
            pair
            .proj_head()
            .cong(
                |arg_ty_0, arg_ty_1, arg_tys_eq| {
                    let arg_ty_0 = arg_ty_0.to_ty();
                    let arg_ty_1 = arg_ty_1.to_ty();

                    arg_ty_0
                    .pi(|arg_0| arg_0.ctx().universe())
                    .pi(|res_ty_0| {
                        let res_ty_0 = {
                            arg_ty_0
                            .weaken_into(&res_ty_0.ctx())
                            .scope(|arg| res_ty_0.app(&arg).to_ty())
                        };

                        arg_ty_1
                        .weaken_into(&res_ty_0.ctx())
                        .pi(|arg_1| arg_1.ctx().universe())
                        .pi(|res_ty_1| {
                            let res_ty_1 = {
                                arg_ty_1
                                .weaken_into(&res_ty_1.ctx())
                                .scope(|arg| res_ty_1.app(&arg).to_ty())
                            };

                            arg_tys_eq
                            .weaken_into(&res_ty_1.ctx())
                            .scoped_tys_equal(res_ty_0.unbind(), res_ty_1.unbind())
                            .pi(|res_tys_eq| {
                                arg_ty_0
                                .weaken_into(&res_tys_eq.ctx())
                                .pi(res_ty_0.unbind())
                                .to_term()
                                .equals(
                                    &arg_ty_1
                                    .weaken_into(&res_tys_eq.ctx())
                                    .pi(res_ty_1.unbind())
                                    .to_term()
                                )
                            })
                        })
                    })
                },
                |arg_ty| {
                    let arg_ty = arg_ty.to_ty();

                    arg_ty
                    .pi(|arg| arg.ctx().universe())
                    .func(|res_ty_0| {
                        arg_ty
                        .weaken_into(&res_ty_0.ctx())
                        .pi(|arg| arg.ctx().universe())
                        .func(|res_ty_1| {
                            res_ty_0
                            .equals(&res_ty_1)
                            .func(|res_tys_eq| {
                                res_tys_eq
                                .map_eq(|res_ty| {
                                    arg_ty
                                    .weaken_into(&res_ty.ctx())
                                    .pi(|arg| res_ty.app(&arg).to_ty())
                                    .to_term()
                                })
                            })
                        })
                    })
                },
            )
            .app(&res_ty_0.map(|_, res_ty| res_ty.to_term()).to_func())
            .app(&res_ty_1.map(|_, res_ty| res_ty.to_term()).to_func())
            .app(&pair.proj_tail())
        });

        let rev = self.var_ty().scope(|eq| {
            eq
            .pi_eq_arg_injective()
            .pair(
                |arg_tys_eq| arg_tys_eq.scoped_tys_equal(res_ty_0.unbind(), res_ty_1.unbind()),
                &eq.pi_eq_res_injective(),
            )
        });

        self.reduce_equality_to_equivprovable_constraint(fwd.unbind(), rev.unbind())
    }

    fn reduce_non_dependent_pair_equality(&self) -> Reduction {
        let (eq_term_0, eq_term_1) = self.var_ty().unwrap_equal();
        let TmKind::Pair { tail_ty, head_term: _, tail_term: tail_0 } = eq_term_0.kind() else {
            panic!("left side of equality is not a pair");
        };
        let TmKind::Pair { tail_ty: _, head_term: _, tail_term: tail_1 } = eq_term_1.kind() else {
            panic!("right side of equality is not a pair");
        };
        let Some(tail_ty) = tail_ty.try_strengthen() else {
            panic!("sigma type is dependent");
        };

        self.reduce_equality_to_equivprovable_constraint(
            |pair| {
                pair
                .proj_head()
                .cong(
                    |head_0, head_1, _head_eq| {
                        head_0
                        .pair(|_| tail_ty.clone(), &tail_0)
                        .equals(
                            &head_1
                            .pair(|_| tail_ty.clone(), &tail_1)
                        )
                    },
                    |head| {
                        pair
                        .proj_tail()
                        .weaken_into(&head.ctx())
                        .map_eq(|tail| head.pair(|_| tail_ty.clone(), &tail))
                    },
                )
            },
            |eq| {
                eq
                .map_eq(|pair| pair.proj_head())
                .pair(
                    |_| tail_0.equals(&tail_1),
                    &eq.map_eq(|pair| pair.proj_tail()),
                )
            },
        )
    }

    fn reduce_dependent_pair_equality(&self) -> Reduction {
        let (eq_term_0, eq_term_1) = self.var_ty().unwrap_equal();
        let TmKind::Pair { tail_ty, head_term: _, tail_term: tail_0 } = eq_term_0.kind() else {
            panic!("left side of equality is not a pair");
        };
        let TmKind::Pair { tail_ty: _, head_term: _, tail_term: tail_1 } = eq_term_1.kind() else {
            panic!("right side of equality is not a pair");
        };

        self.reduce_equality_to_equivprovable_constraint(
            |pair| {
                pair
                .proj_head()
                .cong(
                    |head_0, head_1, head_eq| {
                        tail_ty
                        .bind(&head_0)
                        .pi(|tail_0| {
                            tail_ty
                            .bind(&head_1)
                            .weaken_into(&tail_0.ctx())
                            .pi(|tail_1| {
                                tail_ty
                                .bind_eq(&head_eq)
                                .heterogeneous_equal(
                                    &tail_0,
                                    &tail_1,
                                )
                                .pi(|_tail_eq| {
                                    head_0
                                    .pair(tail_ty.unbind(), &tail_0)
                                    .equals(&head_1.pair(tail_ty.unbind(), &tail_1))
                                })
                            })
                        })
                    },
                    |head| {
                        tail_ty
                        .bind(&head)
                        .func(|tail_0| {
                            tail_ty
                            .bind(&head)
                            .weaken_into(&tail_0.ctx())
                            .func(|tail_1| {
                                tail_0
                                .equals(&tail_1)
                                .func(|tail_eq| {
                                    tail_eq
                                    .map_eq(|tail| {
                                        head.pair(tail_ty.unbind(), &tail)
                                    })
                                })
                            })
                        })
                    },
                )
                .app(&tail_0)
                .app(&tail_1)
                .app(&pair.proj_tail())
            },
            |eq| {
                eq
                .cong(
                    |pair_0, pair_1, _pair_eq| {
                        pair_0
                        .proj_head()
                        .equals(&pair_1.proj_head())
                        .sigma(|head_eq| {
                            tail_ty
                            .bind_eq(&head_eq)
                            .heterogeneous_equal(&pair_0.proj_tail(), &pair_1.proj_tail())
                        })
                    },
                    |pair| {
                        pair
                        .proj_head()
                        .refl()
                        .pair(
                            |head_eq| {
                                tail_ty
                                .bind_eq(&head_eq)
                                .heterogeneous_equal(&pair.proj_tail(), &pair.proj_tail())
                            },
                            &pair.proj_tail().refl(),
                        )
                    },
                )
            },
        )
    }
}

