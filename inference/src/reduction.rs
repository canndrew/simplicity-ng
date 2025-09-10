use crate::priv_prelude::*;

#[derive_where(Clone, Debug)]
#[derive(Contextual)]
#[scheme(S)]
pub(crate) struct Reduction<S: Scheme> {
    body: Scope<S, Tm<S>>,

    // new_ty |- old_ty
    fwd: Scope<S, Tm<S>>,

    // old_ty |- new_ty
    rev: Scope<S, Tm<S>>,

    // (x : old_ty) |-
    //  type_of(infer_scope[x])
    //  ==
    //  type_of(infer_scope[fwd[rev[x]]])
    covering_ty: Scope<S, Tm<S>>,

    // (x : old_ty) |-
    //  covering_ty[x].heterogeneous_equal(
    //      infer_scope[x],
    //      infer_scope[fwd[rev[x]]],
    //  )
    covering: Scope<S, Tm<S>>,
}

impl<S: Scheme> Reduction<S> {
    pub fn old_var_ty(&self) -> Ty<S> {
        self.rev.var_ty()
    }

    pub fn new_var_ty(&self) -> Ty<S> {
        self.fwd.var_ty()
    }

    pub fn reduced_scope(&self) -> Scope<S, Tm<S>> {
        self.fwd.map(|_, term| {
            self.body.bind(&term)
        })
    }

    pub fn and_then(
        &self,
        next_reduction: impl FnOnce(Scope<S, Tm<S>>) -> Reduction<S>,
    ) -> Reduction<S> {
        let next_reduction = next_reduction(self.reduced_scope());
        self.compose(&next_reduction)
    }

    pub fn compose(&self, other: &Reduction<S>) -> Reduction<S> {
        assert_eq!(self.reduced_scope(), other.body);
        assert_eq!(self.new_var_ty(), other.old_var_ty());

        let body = self.body.clone();
        let new_var_ty = other.new_var_ty();
        let fwd = new_var_ty.scope(|new_var_1| {
            self.fwd.bind(&other.fwd.bind(&new_var_1))
        });
        let rev = self.old_var_ty().scope(|old_var| {
            other.rev.bind(&self.rev.bind(&old_var))
        });
        let covering_ty = self.old_var_ty().scope(|old_var| {
            self
            .covering_ty
            .bind(&old_var)
            .transitivity(&other.covering_ty.bind(&self.rev.bind(&old_var)))
        });
        let covering = self.old_var_ty().scope(|old_var| {
            Tm::heterogeneous_transitivity(
                &body.bind(
                    &old_var,
                ),
                &body.bind(
                    &self.fwd.bind(&self.rev.bind(&old_var)),
                ),
                &body.bind(
                    &self.fwd.bind(&other.fwd.bind(&other.rev.bind(&self.rev.bind(&old_var)))),
                ),
                &self.covering_ty.bind(&old_var),
                &other.covering_ty.bind(&self.rev.bind(&old_var)),
                &self.covering.bind(&old_var),
                &other.covering.bind(&self.rev.bind(&old_var)),
            )
        });

        body
        .reduction(
            &new_var_ty,
            fwd.unbind(),
            rev.unbind(),
            covering_ty.unbind(),
            covering.unbind(),
        )
    }

    pub(crate) fn reduce_more(&self, recursion_depth: u32) -> Reduction<S> {
        self.and_then(|scope| scope.reduce_constraint(recursion_depth))
    }
}

#[extension(pub(crate) trait ScopeReduction)]
impl<S: Scheme> Scope<S, Tm<S>> {
    fn reduction(
        &self,
        new_ty: &Ty<S>,
        fwd: impl FnOnce(Tm<S>) -> Tm<S>,
        rev: impl FnOnce(Tm<S>) -> Tm<S>,
        covering_ty: impl FnOnce(Tm<S>) -> Tm<S>,
        covering: impl FnOnce(Tm<S>) -> Tm<S>,
    ) -> Reduction<S> {
        let fwd = new_ty.scope(fwd);
        let rev = self.var_ty().scope(rev);
        let covering_ty = self.var_ty().scope(covering_ty);
        let covering = self.var_ty().scope(covering);

        self.var_ty().with_cons(|term| {
            let term_0 = self.bind(&term);
            let term_1 = self.bind(&fwd.bind(&rev.bind(&term)));

            assert_eq!(
                covering_ty.bind(&term).ty(),
                term_0.ty().to_term().equals(&term_1.ty().to_term()),
            );

            assert_eq!(
                covering.bind(&term).ty(),
                covering_ty.bind(&term).heterogeneous_equal(&term_0, &term_1),
            )
        });

        Reduction { body: self.clone(), fwd, rev, covering_ty, covering }
    }

    fn irreducible(&self) -> Reduction<S> {
        self.reduction(
            &self.var_ty(),
            |term| term,
            |term| term,
            |term| self.bind(&term).ty().to_term().refl(),
            |term| self.bind(&term).refl(),
        )
    }

    fn reduce_unique(
        &self,
        unique_term: &Tm<S>,
        covering_ty: impl FnOnce(Tm<S>) -> Tm<S>,
        covering: impl FnOnce(Tm<S>) -> Tm<S>,
    ) -> Reduction<S> {
        let (body, unique_term) = Ctx::into_common_ctx(self, unique_term);

        let new_var_ty = body.ctx().unit_ty();
        let fwd = new_var_ty.scope(|_| {
            unique_term.clone()
        });
        let rev = body.var_ty().scope(|term| term.ctx().unit_term());
        let covering_ty = body.var_ty().scope(covering_ty);
        let covering = body.var_ty().scope(covering);
        
        self
        .reduction(
            &new_var_ty,
            fwd.unbind(),
            rev.unbind(),
            covering_ty.unbind(),
            covering.unbind(),
        )
    }

    fn reduce_impossible(
        &self,
        never_scope: impl FnOnce(Tm<S>) -> Tm<S>,
    ) -> Reduction<S> {
        let fwd = self.ctx().never().scope(|never| {
            never.explode(|_| self.var_ty())
        });
        let rev = self.var_ty().scope(never_scope);
        let covering_ty = self.var_ty().scope(|term| {
            rev
            .bind(&term)
            .explode(|_| {
                self
                .bind(&term)
                .ty()
                .to_term()
                .equals(
                    &self
                    .bind(&fwd.bind(&rev.bind(&term)))
                    .ty()
                    .to_term()
                )
            })
        });
        let covering = self.var_ty().scope(|term| {
            rev
            .bind(&term)
            .explode(|_| {
                covering_ty
                .bind(&term)
                .heterogeneous_equal(
                    &self.bind(&term),
                    &self.bind(&fwd.bind(&rev.bind(&term))),
                )
            })
        });
        self.reduction(
            &self.ctx().never(),
            fwd.unbind(),
            rev.unbind(),
            covering_ty.unbind(),
            covering.unbind(),
        )
    }

    fn reduce_constraint(&self, recursion_depth: u32) -> Reduction<S> {
        let Some(recursion_depth) = recursion_depth.checked_sub(1) else {
            return self.irreducible();
        };

        if let Some(inner) = self.try_strengthen() {
            if let Some(solution) = self.var_ty().try_find_arbitrary_term() {
                return self.reduce_unique(
                    &solution,
                    |_| inner.ty().to_term().refl(),
                    |_| inner.refl(),
                );
            }
        }

        match self.var_ty().kind() {
            TyKind::Universe |
            TyKind::Nat |
            TyKind::Never |
            TyKind::Unit => {
                self.irreducible()
            },

            TyKind::Equal { eq_term_0, eq_term_1 } => {
                if eq_term_0 == eq_term_1 {
                    return self.reduce_reflexive_equality();
                }

                match (eq_term_0.kind(), eq_term_1.kind()) {
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
                        let reduction = self.reduce_equality(
                            |eq| eq.map_eq(|nat| nat.succs(count.clone())),
                            |eq| eq.nat_succs_injective(count.clone()),
                        );
                        return reduction.reduce_more(recursion_depth);
                    },

                    (
                        TmKind::InjLhs { lhs_term: _, rhs_ty },
                        TmKind::InjLhs { lhs_term: _, rhs_ty: _ },
                    ) => {
                        let reduction = self.reduce_equality(
                            |eq| eq.map_eq(|lhs_term| lhs_term.inj_lhs(&rhs_ty)),
                            |eq| eq.case_eq(),
                        );
                        return reduction.reduce_more(recursion_depth);
                    },

                    (
                        TmKind::InjRhs { lhs_ty, rhs_term: _ },
                        TmKind::InjRhs { lhs_ty: _, rhs_term: _ },
                    ) => {
                        let reduction = self.reduce_equality(
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
            },

            TyKind::Sum { lhs_ty, rhs_ty } => {
                let lhs_scope = lhs_ty.scope(|lhs_term| self.bind(&lhs_term.inj_lhs(&rhs_ty)));
                let rhs_scope = rhs_ty.scope(|rhs_term| self.bind(&rhs_term.inj_rhs(&lhs_ty)));
                let lhs_reduction = lhs_scope.reduce_constraint(recursion_depth);
                let rhs_reduction = rhs_scope.reduce_constraint(recursion_depth);

                let reduction = self.reduce_sum(&lhs_reduction, &rhs_reduction);

                if let TyKind::Never = lhs_reduction.new_var_ty().kind() {
                    return reduction.and_then(|scope| scope.reduce_sum_never_lhs());
                }

                if let TyKind::Never = rhs_reduction.new_var_ty().kind() {
                    return reduction.and_then(|scope| scope.reduce_sum_never_rhs());
                }

                reduction
            },

            TyKind::Sigma { tail_ty } => {
                let old_head_ty = tail_ty.var_ty();

                let tail_reduction = old_head_ty.scope(|old_head| {
                    tail_ty
                    .bind(&old_head)
                    .scope(|old_tail| {
                        self.bind(&old_head.pair(tail_ty.unbind(), &old_tail))
                    })
                    .reduce_constraint(recursion_depth)
                });

                let head_reduction = {
                    old_head_ty
                    .scope(|old_head| {
                        let tail_reduction = tail_reduction.bind(&old_head);

                        tail_reduction
                        .new_var_ty()
                        .func(|new_tail| {
                            self.bind(
                                &old_head
                                .pair(tail_ty.unbind(), &tail_reduction.fwd.bind(&new_tail))
                            )
                        })
                    })
                    .reduce_constraint(recursion_depth)
                };

                let reduction = self.reduce_sigma(&head_reduction, &tail_reduction);

                match tail_reduction.map_out(|_, tail_reduction| {
                    tail_reduction.new_var_ty().kind()
                }) {
                    TyKind::Never => {
                        return reduction.and_then(|scope| scope.reduce_sigma_never_tail());
                    },
                    TyKind::Unit => {
                        return reduction.and_then(|scope| scope.reduce_sigma_unit_tail());
                    },
                    _ => (),
                }

                match head_reduction.new_var_ty().kind() {
                    TyKind::Never => {
                        return reduction.and_then(|scope| scope.reduce_sigma_never_head());
                    },
                    TyKind::Unit => {
                        return reduction.and_then(|scope| scope.reduce_sigma_unit_head());
                    },
                    _ => (),
                }

                if let Some((head, proof)) = {
                    tail_reduction
                    .map(|_, tail_reduction| tail_reduction.new_var_ty())
                    .constrains_own_var()
                } {
                    return {
                        reduction
                        .and_then(|scope| {
                            scope.reduce_sigma_constrained(&head, &proof)
                        })
                        .reduce_more(recursion_depth)
                    };
                }

                if head_reduction.reduced_scope().var_eliminated() {
                    match head_reduction.new_var_ty().kind() {
                        TyKind::Sum { .. } => {
                            return {
                                reduction
                                .and_then(|scope| {
                                    scope.reduce_sigma_sum_head_distribute()
                                })
                                .reduce_more(recursion_depth)
                            };
                        },
                        TyKind::Sigma { .. } => {
                            return {
                                reduction
                                .and_then(|scope| {
                                    scope.reduce_sigma_reassociate_to_tail()
                                })
                                .reduce_more(recursion_depth)
                            };
                        },
                        _ => (),
                    }
                }

                reduction
            },

            _ => self.irreducible(),
        }
    }

    fn reduce_sum(
        &self,
        lhs_reduction: &Reduction<S>,
        rhs_reduction: &Reduction<S>,
    ) -> Reduction<S> {
        let lhs_ty = lhs_reduction.old_var_ty();
        let rhs_ty = rhs_reduction.old_var_ty();

        let new_var_ty = Ty::sum(&lhs_reduction.new_var_ty(), &rhs_reduction.new_var_ty());
        let fwd = {
            new_var_ty
            .scope(|sum| {
                sum
                .case(
                    |_| self.var_ty(),
                    |lhs_term| lhs_reduction.fwd.bind(&lhs_term).inj_lhs(&rhs_ty),
                    |rhs_term| rhs_reduction.fwd.bind(&rhs_term).inj_rhs(&lhs_ty),
                )
            })
        };
        let rev = {
            self
            .var_ty()
            .scope(|sum| {
                sum
                .case(
                    |_| new_var_ty.clone(),
                    |lhs_term| {
                        lhs_reduction
                        .rev
                        .bind(&lhs_term)
                        .inj_lhs(&rhs_reduction.new_var_ty())
                    },
                    |rhs_term| {
                        rhs_reduction
                        .rev
                        .bind(&rhs_term)
                        .inj_rhs(&lhs_reduction.new_var_ty())
                    },
                )
            })
        };
        let covering_ty = {
            self
            .var_ty()
            .scope(|sum| {
                sum
                .case(
                    |sum| {
                        self
                        .bind(&sum)
                        .ty()
                        .to_term()
                        .equals(
                            &self
                            .bind(&fwd.bind(&rev.bind(&sum)))
                            .ty()
                            .to_term()
                        )
                    },
                    |lhs_term| lhs_reduction.covering_ty.bind(&lhs_term),
                    |rhs_term| rhs_reduction.covering_ty.bind(&rhs_term),
                )
            })
        };
        let covering = {
            self
            .var_ty()
            .scope(|sum| {
                sum
                .case(
                    |sum| {
                        covering_ty
                        .bind(&sum)
                        .heterogeneous_equal(
                            &self.bind(&sum),
                            &self.bind(&fwd.bind(&rev.bind(&sum))),
                        )
                    },
                    |lhs_term| lhs_reduction.covering.bind(&lhs_term),
                    |rhs_term| rhs_reduction.covering.bind(&rhs_term),
                )
            })
        };

        self
        .reduction(
            &new_var_ty,
            fwd.unbind(),
            rev.unbind(),
            covering_ty.unbind(),
            covering.unbind(),
        )
    }

    fn reduce_sum_never_lhs(&self) -> Reduction<S> {
        let TyKind::Sum { lhs_ty, rhs_ty } = self.var_ty().kind() else {
            panic!("not scoped over a sum");
        };
        let TyKind::Never = lhs_ty.kind() else {
            panic!("lhs_ty is not never");
        };
        let new_var_ty = rhs_ty.clone();
        let fwd = new_var_ty.scope(|rhs_term| {
            rhs_term.inj_rhs(&lhs_ty)
        });
        let rev = self.var_ty().scope(|sum_term| {
            sum_term
            .case(
                |_| rhs_ty.clone(),
                |lhs_term| lhs_term.explode(|_| rhs_ty.clone()),
                |rhs_term| rhs_term,
            )
        });
        let covering_ty = self.var_ty().scope(|sum_term| {
            sum_term
            .case(
                |sum_term| {
                    self
                    .bind(&sum_term)
                    .ty()
                    .to_term()
                    .equals(
                        &self
                        .bind(&fwd.bind(&rev.bind(&sum_term)))
                        .ty()
                        .to_term()
                    )
                },
                |lhs_term| {
                    lhs_term
                    .explode(|_| {
                        self
                        .bind(&lhs_term.inj_lhs(&rhs_ty))
                        .ty()
                        .to_term()
                        .equals(
                            &self
                            .bind(&fwd.bind(&rev.bind(&lhs_term.inj_lhs(&rhs_ty))))
                            .ty()
                            .to_term()
                        )
                    })
                },
                |rhs_term | {
                    self
                    .bind(&rhs_term.inj_rhs(&lhs_ty))
                    .ty()
                    .to_term()
                    .refl()
                },
            )
        });
        let covering = self.var_ty().scope(|sum_term| {
            sum_term
            .case(
                |sum_term| {
                    covering_ty
                    .bind(&sum_term)
                    .heterogeneous_equal(
                        &self.bind(&sum_term),
                        &self.bind(&fwd.bind(&rev.bind(&sum_term))),
                    )
                },
                |lhs_term| {
                    lhs_term
                    .explode(|_| {
                        covering_ty
                        .bind(&lhs_term.inj_lhs(&rhs_ty))
                        .heterogeneous_equal(
                            &self.bind(&lhs_term.inj_lhs(&rhs_ty)),
                            &self.bind(&fwd.bind(&rev.bind(&lhs_term.inj_lhs(&rhs_ty)))),
                        )
                    })
                },
                |rhs_term| {
                    self
                    .bind(&rhs_term.inj_rhs(&lhs_ty))
                    .refl()
                },
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

    fn reduce_sum_never_rhs(&self) -> Reduction<S> {
        let TyKind::Sum { lhs_ty, rhs_ty } = self.var_ty().kind() else {
            panic!("not scoped over a sum");
        };
        let TyKind::Never = rhs_ty.kind() else {
            panic!("rhs_ty is not never");
        };

        let new_var_ty = lhs_ty.clone();
        let fwd = new_var_ty.scope(|lhs_term| {
            lhs_term.inj_lhs(&rhs_ty)
        });
        let rev = self.var_ty().scope(|sum_term| {
            sum_term
            .case(
                |_| lhs_ty.clone(),
                |lhs_term| lhs_term,
                |rhs_term| rhs_term.explode(|_| lhs_ty.clone()),
            )
        });
        let covering_ty = self.var_ty().scope(|sum_term| {
            sum_term
            .case(
                |sum_term| {
                    self
                    .bind(&sum_term)
                    .ty()
                    .to_term()
                    .equals(
                        &self
                        .bind(&fwd.bind(&rev.bind(&sum_term)))
                        .ty()
                        .to_term()
                    )
                },
                |lhs_term| {
                    self
                    .bind(&lhs_term.inj_lhs(&rhs_ty))
                    .ty()
                    .to_term()
                    .refl()
                },
                |rhs_term| {
                    rhs_term
                    .explode(|_| {
                        self
                        .bind(&rhs_term.inj_rhs(&lhs_ty))
                        .ty()
                        .to_term()
                        .equals(
                            &self
                            .bind(&fwd.bind(&rev.bind(&rhs_term.inj_rhs(&lhs_ty))))
                            .ty()
                            .to_term()
                        )
                    })
                },
            )
        });
        let covering = self.var_ty().scope(|sum_term| {
            sum_term
            .case(
                |sum_term| {
                    covering_ty
                    .bind(&sum_term)
                    .heterogeneous_equal(
                        &self.bind(&sum_term),
                        &self.bind(&fwd.bind(&rev.bind(&sum_term))),
                    )
                },
                |lhs_term| {
                    self
                    .bind(&lhs_term.inj_lhs(&rhs_ty))
                    .refl()
                },
                |rhs_term| {
                    rhs_term
                    .explode(|_| {
                        covering_ty
                        .bind(&rhs_term.inj_rhs(&lhs_ty))
                        .heterogeneous_equal(
                            &self.bind(&rhs_term.inj_rhs(&lhs_ty)),
                            &self.bind(&fwd.bind(&rev.bind(&rhs_term.inj_rhs(&lhs_ty)))),
                        )
                    })
                },
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

    fn reduce_sigma(
        &self,
        head_reduction: &Reduction<S>,
        tail_reduction: &Scope<S, Reduction<S>>,
    ) -> Reduction<S> {
        let tail_ty = tail_reduction.map(|_, tail_reduction| tail_reduction.old_var_ty());

        let new_var_ty = {
            head_reduction
            .new_var_ty()
            .sigma(|new_head| {
                tail_reduction
                .bind(&head_reduction.fwd.bind(&new_head))
                .new_var_ty()
            })
        };
        
        let fwd = {
            new_var_ty
            .scope(|new_pair| {
                let new_head = new_pair.proj_head();
                let new_tail = new_pair.proj_tail();

                let old_head = head_reduction.fwd.bind(&new_head);
                let old_tail = tail_reduction.bind(&old_head).fwd.bind(&new_tail);
                
                old_head.pair(tail_ty.unbind(), &old_tail)
            })
        };

        let rev = {
            self
            .var_ty()
            .scope(|old_pair| {
                let old_head = old_pair.proj_head();
                let old_tail = old_pair.proj_tail();

                let new_head = head_reduction.rev.bind(&old_head);
                let new_tail = tail_reduction.bind(&old_head).rev.bind(&old_tail);

                let new_tail = {
                    head_reduction
                    .covering_ty
                    .bind(&old_head)
                    .pi_eq_arg_injective()
                    .transport(&new_tail)
                };

                new_head
                .pair(
                    |new_head| {
                        tail_reduction
                        .bind(&head_reduction.fwd.bind(&new_head))
                        .new_var_ty()
                    },
                    &new_tail,
                )
            })
        };

        let covering_ty = {
            self
            .var_ty()
            .scope(|old_pair| {
                let old_head = old_pair.proj_head();
                let old_tail = old_pair.proj_tail();
                let tail_reduction = tail_reduction.bind(&old_head);

                head_reduction
                .covering_ty
                .bind(&old_head)
                .pi_eq_cong(
                    |new_tail_ty_0, _new_tail_ty_1, body_ty_0, body_ty_1, pi_tys_eq| {
                        new_tail_ty_0
                        .pi(|new_tail| {
                            new_tail
                            .ctx()
                            .universe()
                            .pi(|pre_body_ty| {
                                pre_body_ty
                                .equals(&body_ty_0.app(&new_tail))
                                .pi(|_pre_body_tys_eq| {
                                    pre_body_ty
                                    .equals(
                                        &body_ty_1
                                        .app(
                                            &pi_tys_eq
                                            .pi_eq_arg_injective()
                                            .transport(&new_tail)
                                        )
                                    )
                                })
                            })
                        })
                    },
                    |new_tail_ty, body_ty| {
                        new_tail_ty
                        .func(|new_tail| {
                            new_tail
                            .ctx()
                            .universe()
                            .func(|pre_body_ty| {
                                pre_body_ty
                                .equals(&body_ty.app(&new_tail))
                                .func(|pre_body_tys_eq| pre_body_tys_eq)
                            })
                        })
                    },
                )
                .app(&tail_reduction.rev.bind(&old_tail))
                .app(
                    &self
                    .bind(&old_pair)
                    .ty()
                    .to_term()
                )
                .app(&tail_reduction.covering_ty.bind(&old_tail))
            })
        };

        let covering = {
            self
            .var_ty()
            .scope(|old_pair| {
                let old_head = old_pair.proj_head();
                let old_tail = old_pair.proj_tail();

                let new_head = head_reduction.rev.bind(&old_head);
                let round_trip_head = head_reduction.fwd.bind(&new_head);

                let round_trip_tail_reduced = tail_reduction.bind(&round_trip_head);
                let tail_reduction = tail_reduction.bind(&old_head);

                head_reduction
                .covering_ty
                .bind(&old_head)
                .pi_eq_cong(
                    |new_tail_ty_0, new_tail_ty_1, body_ty_0, body_ty_1, pi_tys_eq| {
                        new_tail_ty_0
                        .pi(|new_tail| {
                            new_tail
                            .ctx()
                            .universe()
                            .pi(|pre_body_ty| {
                                pre_body_ty
                                .equals(&body_ty_0.app(&new_tail))
                                .pi(|pre_body_tys_eq| {
                                    new_tail_ty_0
                                    .weaken_into(&pre_body_tys_eq.ctx())
                                    .pi(|new_tail| body_ty_0.app(&new_tail).to_ty())
                                    .pi(|body_0| {
                                        new_tail_ty_1
                                        .weaken_into(&body_0.ctx())
                                        .pi(|new_tail| body_ty_1.app(&new_tail).to_ty())
                                        .pi(|body_1| {
                                            pi_tys_eq
                                            .weaken_into(&body_1.ctx())
                                            .heterogeneous_equal(&body_0, &body_1)
                                            .pi(|bodys_eq| {
                                                pre_body_ty
                                                .weaken_into(&bodys_eq.ctx())
                                                .to_ty()
                                                .pi(|pre_body| {
                                                    pre_body_tys_eq
                                                    .weaken_into(&pre_body.ctx())
                                                    .heterogeneous_equal(
                                                        &pre_body,
                                                        &body_0.app(&new_tail),
                                                    )
                                                    .pi(|pre_bodys_eq| {
                                                        pi_tys_eq
                                                        .weaken_into(&pre_bodys_eq.ctx())
                                                        .pi_eq_cong(
                                                            |new_tail_ty_0, _new_tail_ty_1, body_ty_0, body_ty_1, pi_tys_eq| {
                                                                new_tail_ty_0
                                                                .pi(|new_tail| {
                                                                    new_tail
                                                                    .ctx()
                                                                    .universe()
                                                                    .pi(|pre_body_ty| {
                                                                        pre_body_ty
                                                                        .equals(&body_ty_0.app(&new_tail))
                                                                        .pi(|_pre_body_tys_eq| {
                                                                            pre_body_ty
                                                                            .equals(
                                                                                &body_ty_1
                                                                                .app(
                                                                                    &pi_tys_eq
                                                                                    .pi_eq_arg_injective()
                                                                                    .transport(&new_tail)
                                                                                )
                                                                            )
                                                                        })
                                                                    })

                                                                })
                                                            },
                                                            |new_tail_ty, body_ty| {
                                                                new_tail_ty
                                                                .func(|new_tail| {
                                                                    new_tail
                                                                    .ctx()
                                                                    .universe()
                                                                    .func(|pre_body_ty| {
                                                                        pre_body_ty
                                                                        .equals(&body_ty.app(&new_tail))
                                                                        .func(|pre_body_tys_eq| pre_body_tys_eq)
                                                                    })
                                                                })
                                                            },
                                                        )
                                                        .app(&new_tail)
                                                        .app(&pre_body_ty)
                                                        .app(&pre_body_tys_eq)
                                                        .heterogeneous_equal(
                                                            &pre_body,
                                                            &body_1
                                                            .app(
                                                                &pi_tys_eq
                                                                .pi_eq_arg_injective()
                                                                .transport(&new_tail)
                                                            ),
                                                        )
                                                    })
                                                })
                                            })
                                        })
                                    })
                                })
                            })
                        })
                    },
                    |new_tail_ty, body_ty| {
                        new_tail_ty
                        .func(|new_tail| {
                            new_tail
                            .ctx()
                            .universe()
                            .func(|pre_body_ty| {
                                pre_body_ty
                                .equals(&body_ty.app(&new_tail))
                                .func(|pre_body_tys_eq| {
                                    new_tail_ty
                                    .weaken_into(&pre_body_tys_eq.ctx())
                                    .pi(|new_tail| body_ty.app(&new_tail).to_ty())
                                    .func(|body_0| {
                                        new_tail_ty
                                        .weaken_into(&body_0.ctx())
                                        .pi(|new_tail| body_ty.app(&new_tail).to_ty())
                                        .func(|body_1| {
                                            body_0
                                            .equals(&body_1)
                                            .func(|bodys_eq| {
                                                pre_body_ty
                                                .to_ty()
                                                .weaken_into(&bodys_eq.ctx())
                                                .func(|pre_body| {
                                                    pre_body_tys_eq
                                                    .weaken_into(&pre_body.ctx())
                                                    .heterogeneous_equal(
                                                        &pre_body,
                                                        &body_0.app(&new_tail),
                                                    )
                                                    .func(|pre_bodys_eq| {
                                                        bodys_eq
                                                        .weaken_into(&pre_bodys_eq.ctx())
                                                        .cong(
                                                            |body_0, body_1, bodys_eq| {
                                                                pre_body_tys_eq
                                                                .weaken_into(&bodys_eq.ctx())
                                                                .heterogeneous_equal(
                                                                    &pre_body,
                                                                    &body_0.app(&new_tail),
                                                                )
                                                                .pi(|_pre_bodys_eq| {
                                                                    pre_body_tys_eq
                                                                    .heterogeneous_equal(
                                                                        &pre_body,
                                                                        &body_1.app(&new_tail),
                                                                    )
                                                                })
                                                            },
                                                            |body| {
                                                                pre_body_tys_eq
                                                                .weaken_into(&body.ctx())
                                                                .heterogeneous_equal(
                                                                    &pre_body,
                                                                    &body.app(&new_tail),
                                                                )
                                                                .func(|pre_bodys_eq| pre_bodys_eq)
                                                            },
                                                        )
                                                        .app(&pre_bodys_eq)
                                                    })
                                                })
                                            })
                                        })
                                    })
                                })
                            })
                        })
                    },
                )
                .app(&tail_reduction.rev.bind(&old_tail))
                .app(
                    &self
                    .bind(&old_pair)
                    .ty()
                    .to_term(),
                )
                .app(&tail_reduction.covering_ty.bind(&old_tail))
                .app(
                    &tail_reduction
                    .new_var_ty()
                    .func(|new_tail| {
                        self
                        .bind(
                            &old_head
                            .pair(tail_ty.unbind(), &tail_reduction.fwd.bind(&new_tail))
                        )
                    })
                )
                .app(
                    &round_trip_tail_reduced
                    .new_var_ty()
                    .func(|new_tail| {
                        self
                        .bind(
                            &round_trip_head
                            .pair(tail_ty.unbind(), &round_trip_tail_reduced.fwd.bind(&new_tail))
                        )
                    })
                )
                .app(&head_reduction.covering.bind(&old_head))
                .app(&self.bind(&old_pair))
                .app(&tail_reduction.covering.bind(&old_tail))
            })
        };

        self.reduction(
            &new_var_ty,
            fwd.unbind(),
            rev.unbind(),
            covering_ty.unbind(),
            covering.unbind(),
        )
    }

    fn reduce_sigma_never_tail(&self) -> Reduction<S> {
        self.reduce_impossible(|pair| {
            pair.proj_tail()
        })
    }

    fn reduce_sigma_never_head(&self) -> Reduction<S> {
        self.reduce_impossible(|pair| {
            pair.proj_head()
        })
    }

    fn reduce_sigma_unit_tail(&self) -> Reduction<S> {
        let TyKind::Sigma { tail_ty } = self.var_ty().kind() else {
            panic!("not scoped over a sigma");
        };
        debug_assert!(matches!(tail_ty.map_out(|_, tail_ty| tail_ty.kind()), TyKind::Unit));
        let head_ty = tail_ty.var_ty();

        let new_var_ty = head_ty.clone();
        let fwd = head_ty.scope(|head| {
            head.pair(|head| head.ctx().unit_ty(), &head.ctx().unit_term())
        });
        let rev = self.var_ty().scope(|pair| {
            pair.proj_head()
        });
        let covering_ty = self.var_ty().scope(|pair| {
            self.bind(&pair).ty().to_term().refl()
        });
        let covering = self.var_ty().scope(|pair| {
            self.bind(&pair).refl()
        });

        self.reduction(
            &new_var_ty,
            fwd.unbind(),
            rev.unbind(),
            covering_ty.unbind(),
            covering.unbind(),
        )
    }

    fn reduce_sigma_unit_head(&self) -> Reduction<S> {
        let TyKind::Sigma { tail_ty } = self.var_ty().kind() else {
            panic!("not scoped over a sigma");
        };

        let new_var_ty = tail_ty.bind(&self.ctx().unit_term());
        let fwd = new_var_ty.scope(|tail| {
            tail
            .ctx()
            .unit_term()
            .pair(tail_ty.unbind(), &tail)
        });
        let rev = self.var_ty().scope(|pair| {
            pair.proj_tail()
        });
        let covering_ty = self.var_ty().scope(|pair| {
            self.bind(&pair).ty().to_term().refl()
        });
        let covering = self.var_ty().scope(|pair| {
            self.bind(&pair).refl()
        });

        self.reduction(
            &new_var_ty,
            fwd.unbind(),
            rev.unbind(),
            covering_ty.unbind(),
            covering.unbind(),
        )
    }

    fn reduce_sigma_sum_head_distribute(&self) -> Reduction<S> {
        let TyKind::Sigma { tail_ty } = self.var_ty().kind() else {
            panic!("not scoped over a sigma");
        };
        let TyKind::Sum { lhs_ty, rhs_ty } = tail_ty.var_ty().kind() else {
            panic!("head type of sigma is not a sum");
        };

        let new_var_ty = Ty::sum(
            &lhs_ty.sigma(|lhs| tail_ty.bind(&lhs.inj_lhs(&rhs_ty))),
            &rhs_ty.sigma(|rhs| tail_ty.bind(&rhs.inj_rhs(&lhs_ty))),
        );
        let fwd = new_var_ty.scope(|sum_pair| {
            sum_pair
            .case(
                |_| self.var_ty(),
                |lhs_pair| {
                    lhs_pair
                    .proj_head()
                    .inj_lhs(&rhs_ty)
                    .pair(tail_ty.unbind(), &lhs_pair.proj_tail())
                },
                |rhs_pair| {
                    rhs_pair
                    .proj_head()
                    .inj_rhs(&lhs_ty)
                    .pair(tail_ty.unbind(), &rhs_pair.proj_tail())
                },
            )
        });
        let rev = self.var_ty().scope(|pair| {
            pair
            .proj_head()
            .case(
                |sum| {
                    tail_ty
                    .bind(&sum)
                    .pi(|_| new_var_ty.clone())
                },
                |lhs| {
                    tail_ty
                    .bind(&lhs.inj_lhs(&rhs_ty))
                    .func(|tail| {
                        lhs
                        .weaken_into(&tail.ctx())
                        .pair(
                            |lhs| tail_ty.bind(&lhs.inj_lhs(&rhs_ty)),
                            &tail,
                        )
                        .inj_lhs(&rhs_ty.sigma(|rhs| tail_ty.bind(&rhs.inj_rhs(&lhs_ty))))
                    })
                },
                |rhs| {
                    tail_ty
                    .bind(&rhs.inj_rhs(&lhs_ty))
                    .func(|tail| {
                        rhs
                        .weaken_into(&tail.ctx())
                        .pair(
                            |rhs| tail_ty.bind(&rhs.inj_rhs(&lhs_ty)),
                            &tail,
                        )
                        .inj_rhs(&lhs_ty.sigma(|lhs| tail_ty.bind(&lhs.inj_lhs(&rhs_ty))))
                    })
                },
            )
            .app(&pair.proj_tail())
        });
        let covering_ty = self.var_ty().scope(|pair| {
            pair
            .proj_head()
            .case(
                |sum| {
                    tail_ty
                    .bind(&sum)
                    .pi(|tail| {
                        let pair = sum.weaken_into(&tail.ctx()).pair(tail_ty.unbind(), &tail);

                        self
                        .bind(&pair)
                        .ty()
                        .to_term()
                        .equals(
                            &self
                            .bind(&fwd.bind(&rev.bind(&pair)))
                            .ty()
                            .to_term()
                        )
                    })
                },
                |lhs| {
                    let sum = lhs.inj_lhs(&rhs_ty);
                    tail_ty
                    .bind(&sum)
                    .func(|tail| {
                        let pair = sum.weaken_into(&tail.ctx()).pair(tail_ty.unbind(), &tail);

                        self
                        .bind(&pair)
                        .ty()
                        .to_term()
                        .refl()
                    })
                },
                |rhs| {
                    let sum = rhs.inj_rhs(&lhs_ty);
                    tail_ty
                    .bind(&sum)
                    .func(|tail| {
                        let pair = sum.weaken_into(&tail.ctx()).pair(tail_ty.unbind(), &tail);

                        self
                        .bind(&pair)
                        .ty()
                        .to_term()
                        .refl()
                    })
                },
            )
            .app(&pair.proj_tail())
        });
        let covering = self.var_ty().scope(|pair| {
            pair
            .proj_head()
            .case(
                |sum| {
                    tail_ty
                    .bind(&sum)
                    .pi(|tail| {
                        let pair = sum.weaken_into(&tail.ctx()).pair(tail_ty.unbind(), &tail);

                        covering_ty
                        .bind(&pair)
                        .heterogeneous_equal(
                            &self.bind(&pair),
                            &self.bind(&fwd.bind(&rev.bind(&pair))),
                        )
                    })
                },
                |lhs| {
                    let sum = lhs.inj_lhs(&rhs_ty);
                    tail_ty
                    .bind(&sum)
                    .func(|tail| {
                        let pair = sum.weaken_into(&tail.ctx()).pair(tail_ty.unbind(), &tail);

                        self
                        .bind(&pair)
                        .refl()
                    })
                },
                |rhs| {
                    let sum = rhs.inj_rhs(&lhs_ty);
                    tail_ty
                    .bind(&sum)
                    .func(|tail| {
                        let pair = sum.weaken_into(&tail.ctx()).pair(tail_ty.unbind(), &tail);

                        self
                        .bind(&pair)
                        .refl()
                    })
                },
            )
            .app(&pair.proj_tail())
        });

        self
        .reduction(
            &new_var_ty,
            fwd.unbind(),
            rev.unbind(),
            covering_ty.unbind(),
            covering.unbind(),
        )
    }

    fn reduce_sigma_reassociate_to_tail(&self) -> Reduction<S> {
        let TyKind::Sigma { tail_ty: old_tail_ty } = self.var_ty().kind() else {
            panic!("not scoped over a sigma");
        };
        let TyKind::Sigma { tail_ty: middle_ty } = old_tail_ty.var_ty().kind() else {
            panic!("not scoped over a head-nested sigma");
        };
        let new_tail_ty = middle_ty.map(|head, bound_middle_ty| {
            bound_middle_ty.scope(|middle| {
                old_tail_ty.bind(
                    &head.pair(middle_ty.unbind(), &middle)
                )
            })
        });

        let new_var_ty = new_tail_ty.map(|_, tail_ty| tail_ty.to_sigma()).to_sigma();

        let fwd = new_var_ty.scope(|pair| {
            pair
            .proj_head()
            .pair(middle_ty.unbind(), &pair.proj_tail().proj_head())
            .pair(old_tail_ty.unbind(), &pair.proj_tail().proj_tail())
        });
        let rev = self.var_ty().scope(|pair| {
            pair
            .proj_head()
            .proj_head()
            .pair(
                |head| new_tail_ty.bind(&head).to_sigma(),
                &pair
                .proj_head()
                .proj_tail()
                .pair(
                    |middle| new_tail_ty.bind(&pair.proj_head().proj_head()).bind(&middle),
                    &pair.proj_tail(),
                )
            )
        });

        let covering_ty = self.map(|_, body| body.ty().to_term().refl());
        let covering = self.map(|_, body| body.refl());

        self
        .reduction(
            &new_var_ty,
            fwd.unbind(),
            rev.unbind(),
            covering_ty.unbind(),
            covering.unbind(),
        )
    }

    fn reduce_sigma_constrained(
        &self,
        head: &Tm<S>,
        proof: &Scope<S, Scope<S, Tm<S>>>,
    ) -> Reduction<S> {
        let TyKind::Sigma { tail_ty: old_tail_ty } = self.var_ty().kind() else {
            panic!("not scoped over a sigma");
        };

        let new_var_ty = old_tail_ty.bind(&head);
        let fwd = new_var_ty.scope(|new_tail| {
            head.pair(old_tail_ty.unbind(), &new_tail)
        });
        let rev = self.var_ty().scope(|old_pair| {
            let old_head = old_pair.proj_head();
            let old_tail = old_pair.proj_tail();
            let head_eq = proof.bind(&old_head).bind(&old_tail);

            old_tail_ty.bind_eq(&head_eq).transport(&old_tail)
        });
        let covering_ty = self.var_ty().scope(|old_pair| {
            let old_head = old_pair.proj_head();
            let old_tail = old_pair.proj_tail();

            proof
            .bind(&old_head)
            .bind(&old_tail)
            .cong(
                |head_0, head_1, head_eq| {
                    old_tail_ty
                    .bind(&head_0)
                    .pi(|tail| {
                        self
                        .bind(&head_0.pair(old_tail_ty.unbind(), &tail))
                        .ty()
                        .to_term()
                        .equals(
                            &self
                            .bind(
                                &head_1
                                .pair(
                                    old_tail_ty.unbind(),
                                    &old_tail_ty.bind_eq(&head_eq).transport(&tail),
                                )
                            )
                            .ty()
                            .to_term(),
                        )
                    })
                },
                |head| {
                    old_tail_ty
                    .bind(&head)
                    .func(|tail| {
                        self
                        .bind(&head.pair(old_tail_ty.unbind(), &tail))
                        .ty()
                        .to_term()
                        .refl()
                    })
                },
            )
            .app(&old_tail)
        });
        let covering = self.var_ty().scope(|old_pair| {
            let old_head = old_pair.proj_head();
            let old_tail = old_pair.proj_tail();

            proof
            .bind(&old_head)
            .bind(&old_tail)
            .cong(
                |head_0, head_1, head_eq| {
                    old_tail_ty
                    .bind(&head_0)
                    .pi(|tail| {
                        head_eq
                        .weaken_into(&tail.ctx())
                        .cong(
                            |head_0, head_1, head_eq| {
                                old_tail_ty
                                .bind(&head_0)
                                .pi(|tail| {
                                    self
                                    .bind(&head_0.pair(old_tail_ty.unbind(), &tail))
                                    .ty()
                                    .to_term()
                                    .equals(
                                        &self
                                        .bind(
                                            &head_1
                                            .pair(
                                                old_tail_ty.unbind(),
                                                &old_tail_ty.bind_eq(&head_eq).transport(&tail),
                                            )
                                        )
                                        .ty()
                                        .to_term(),
                                    )
                                })
                            },
                            |head| {
                                old_tail_ty
                                .bind(&head)
                                .func(|tail| {
                                    self
                                    .bind(&head.pair(old_tail_ty.unbind(), &tail))
                                    .ty()
                                    .to_term()
                                    .refl()
                                })
                            },
                        )
                        .app(&tail)
                        .heterogeneous_equal(
                            &self
                            .bind(&head_0.pair(old_tail_ty.unbind(), &tail)),
                            &self
                            .bind(
                                &head_1
                                .pair(
                                    old_tail_ty.unbind(),
                                    &old_tail_ty.bind_eq(&head_eq).transport(&tail),
                                ),
                            ),
                        )
                    })
                },
                |head| {
                    old_tail_ty
                    .bind(&head)
                    .func(|tail| {
                        self
                        .bind(&head.pair(old_tail_ty.unbind(), &tail))
                        .refl()
                    })
                },
            )
            .app(&old_tail)
        });

        self
        .reduction(
            &new_var_ty,
            fwd.unbind(),
            rev.unbind(),
            covering_ty.unbind(),
            covering.unbind(),
        )
    }

    fn reduce_equality(
        &self,
        fwd: impl FnOnce(Tm<S>) -> Tm<S>,
        rev: impl FnOnce(Tm<S>) -> Tm<S>,
    ) -> Reduction<S> {
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

    fn reduce_reflexive_equality(&self) -> Reduction<S> {
        let TyKind::Equal { eq_term_0, eq_term_1 } = self.var_ty().kind() else {
            panic!("not scoped over an equality");
        };
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

    fn reduce_equal_type_equality(&self) -> Reduction<S> {
        let TyKind::Equal { eq_term_0, eq_term_1 } = self.var_ty().kind() else {
            panic!("not scoped over an equality");
        };
        let TyKind::Equal {
            eq_term_0: eq_term_0_0, eq_term_1: eq_term_1_0,
        } = eq_term_0.to_ty().kind() else {
            panic!("left side of equality is not an equality type");
        };
        let TyKind::Equal {
            eq_term_0: eq_term_0_1, eq_term_1: eq_term_1_1,
        } = eq_term_1.to_ty().kind() else {
            panic!("left side of equality is not an equality type");
        };

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

        self.reduce_equality(fwd.unbind(), rev.unbind())
    }

    fn reduce_sum_type_equality(&self) -> Reduction<S> {
        let TyKind::Equal { eq_term_0, eq_term_1 } = self.var_ty().kind() else {
            panic!("not scoped over an equality");
        };
        let TyKind::Sum { lhs_ty: lhs_ty_0, rhs_ty: rhs_ty_0 } = eq_term_0.to_ty().kind() else {
            panic!("left side of equality is not a sum type");
        };
        let TyKind::Sum { lhs_ty: lhs_ty_1, rhs_ty: rhs_ty_1 } = eq_term_1.to_ty().kind() else {
            panic!("right side of equality is not a sum type");
        };

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

        self.reduce_equality(fwd.unbind(), rev.unbind())
    }

    fn reduce_sigma_type_equality(&self) -> Reduction<S> {
        let TyKind::Equal { eq_term_0, eq_term_1 } = self.var_ty().kind() else {
            panic!("not scoped over an equality");
        };
        let TyKind::Sigma { tail_ty: tail_ty_0 } = eq_term_0.to_ty().kind() else {
            panic!("left side of equality is not a sigma type");
        };
        let TyKind::Sigma { tail_ty: tail_ty_1 } = eq_term_1.to_ty().kind() else {
            panic!("right side of equality is not a sigma type");
        };

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

        self.reduce_equality(fwd.unbind(), rev.unbind())
    }

    fn reduce_pi_type_equality(&self) -> Reduction<S> {
        let TyKind::Equal { eq_term_0, eq_term_1 } = self.var_ty().kind() else {
            panic!("not scoped over an equality");
        };
        let TyKind::Pi { res_ty: res_ty_0 } = eq_term_0.to_ty().kind() else {
            panic!("left side of equality is not a pi type");
        };
        let TyKind::Pi { res_ty: res_ty_1 } = eq_term_1.to_ty().kind() else {
            panic!("right side of equality is not a pi type");
        };

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

        self.reduce_equality(fwd.unbind(), rev.unbind())
    }

    fn reduce_non_dependent_pair_equality(&self) -> Reduction<S> {
        let TyKind::Equal { eq_term_0, eq_term_1 } = self.var_ty().kind() else {
            panic!("not scoped over an equality");
        };
        let TmKind::Pair { tail_ty, head_term: _, tail_term: tail_0 } = eq_term_0.kind() else {
            panic!("left side of equality is not a pair");
        };
        let TmKind::Pair { tail_ty: _, head_term: _, tail_term: tail_1 } = eq_term_1.kind() else {
            panic!("right side of equality is not a pair");
        };
        let Some(tail_ty) = tail_ty.try_strengthen() else {
            panic!("sigma type is dependent");
        };

        self.reduce_equality(
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

    fn reduce_dependent_pair_equality(&self) -> Reduction<S> {
        let TyKind::Equal { eq_term_0, eq_term_1 } = self.var_ty().kind() else {
            panic!("not scoped over an equality");
        };
        let TmKind::Pair { tail_ty, head_term: _, tail_term: tail_0 } = eq_term_0.kind() else {
            panic!("left side of equality is not a pair");
        };
        let TmKind::Pair { tail_ty: _, head_term: _, tail_term: tail_1 } = eq_term_1.kind() else {
            panic!("right side of equality is not a pair");
        };

        self.reduce_equality(
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

    fn reduce_over_iso(
        &self,
        iso: &Iso<S>,
    ) -> Reduction<S> {
        let new_var_ty = iso.output_ty();
        let fwd = new_var_ty.scope(|new_term| iso.rev(&new_term));
        let rev = self.var_ty().scope(|old_term| iso.fwd(&old_term));

        let covering_ty = self.var_ty().scope(|old_term| {
            self
            .map(|_, body| body.ty())
            .bind_eq(&iso.fwd_rev(&old_term).symmetry())
        });
        let covering = self.var_ty().scope(|old_term| {
            iso
            .fwd_rev(&old_term)
            .symmetry()
            .cong(
                |old_term_0, old_term_1, old_term_eq| {
                    self
                    .map(|_, body| body.ty())
                    .bind_eq(&old_term_eq)
                    .heterogeneous_equal(
                        &self.bind(&old_term_0),
                        &self.bind(&old_term_1),
                    )
                },
                |old_term| self.bind(&old_term).refl(),
            )
        });

        self
        .reduction(
            &new_var_ty,
            fwd.unbind(),
            rev.unbind(),
            covering_ty.unbind(),
            covering.unbind(),
        )
    }
}

