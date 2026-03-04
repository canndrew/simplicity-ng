use crate::priv_prelude::*;

#[expect(unused)]
impl Scope<Tm> {
    /*
    pub(crate) fn reduce_constraint_sigma(&self, recursion_depth: u32) -> Reduction {
        /*
        let tail_ty = self.var_ty().unwrap_sigma();
        let head_ty = tail_ty.var_ty();
        if tail_ty.try_strengthen().is_some() {
            return self.reduce_constraint_non_dependent_sigma(recursion_depth);
        }
        */

        let mut recursion_depth = recursion_depth;

        let mut reduction = self.reduce_constraint_sigma_tail(recursion_depth);
        let reduced_tail_ty = reduction.new_var_ty().unwrap_sigma();
        match reduced_tail_ty.map_out(|_, tail_ty| tail_ty.kind()) {
            TyKind::Never => {
                return {
                    reduction
                    .and_then(|scope| scope.reduce_sigma_never_tail())
                };
            },
            TyKind::Unit => {
                return {
                    reduction
                    .and_then(|scope| scope.reduce_sigma_unit_tail())
                    .reduce_more(recursion_depth)
                };
            },
            _ => (),
        }

        loop {
            let tail_ty = reduction.new_var_ty().unwrap_sigma();
            let old_head_ty = tail_ty.var_ty();
            reduction = {
                reduction
                .and_then(|scope| scope.reduce_constraint_sigma_head(recursion_depth))
            };
            let tail_ty = reduction.new_var_ty().unwrap_sigma();
            let new_head_ty = tail_ty.var_ty();

            match new_head_ty.kind() {
                TyKind::Never => {
                    return {
                        reduction
                        .and_then(|scope| scope.reduce_sigma_never_head())
                    };
                },
                TyKind::Unit => {
                    return {
                        reduction
                        .and_then(|scope| scope.reduce_sigma_unit_head())
                        .reduce_more(recursion_depth)
                    };
                },
                _ => (),
            }

            if let Some((head, proof)) = tail_ty.constrains_own_var() {
                return {
                    reduction
                    .and_then(|scope| {
                        scope.reduce_sigma_constrained(&head, &proof)
                    })
                    .reduce_more(recursion_depth)
                };
            }

            if tail_ty.var_eliminated() {
                match new_head_ty.kind() {
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

            if old_head_ty == new_head_ty {
                return reduction;
            }
            let Some(next_recursion_depth) = recursion_depth.checked_sub(1) else {
                return reduction;
            };
            recursion_depth = next_recursion_depth;

            let old_tail_ty = tail_ty;
            reduction = {
                reduction
                .and_then(|scope| scope.reduce_constraint_sigma_tail(recursion_depth))
            };
            let new_tail_ty = reduction.new_var_ty().unwrap_sigma();

            match new_tail_ty.map_out(|_, new_tail_ty| new_tail_ty.kind()) {
                TyKind::Never => {
                    return {
                        reduction
                        .and_then(|scope| scope.reduce_sigma_never_tail())
                    };
                },
                TyKind::Unit => {
                    return {
                        reduction
                        .and_then(|scope| scope.reduce_sigma_unit_tail())
                        .reduce_more(recursion_depth)
                    };
                },
                _ => (),
            }

            if old_tail_ty == new_tail_ty {
                return reduction;
            }
        }
    }

    fn reduce_constraint_sigma_head(&self, recursion_depth: u32) -> Reduction {
        let (var_tag, var_ty) = self.var_tag_and_ty();
        let tail_ty = var_ty.unwrap_sigma();
        let (head_tag, old_head_ty) = tail_ty.var_tag_and_ty();

        let head_reduction = {
            old_head_ty
            .scope(&head_tag, |old_head| {
                tail_ty
                .bind(&old_head)
                .func(&var_tag, |tail| {
                    self
                    .bind(&old_head.pair(&head_tag, tail_ty.unbind(), &tail))
                })
            })
            .reduce_constraint(recursion_depth)
        };

        let new_head_ty = head_reduction.new_var_ty();
        let new_tail_ty = new_head_ty.scope(&head_tag, |new_head| {
            tail_ty.bind(&head_reduction.fwd(&new_head))
        });
        let new_var_ty = new_tail_ty.to_sigma();

        let fwd = new_var_ty.scope(&var_tag, |new_pair| {
            let new_head = new_pair.proj_head();
            let tail = new_pair.proj_tail();

            head_reduction
            .fwd(&new_head)
            .pair(&head_tag, tail_ty.unbind(), &tail)
        });

        let rev = var_ty.scope(&var_tag, |old_pair| {
            let old_head = old_pair.proj_head();
            let tail = old_pair.proj_tail();

            let new_head = head_reduction.rev(&old_head);
            let tail = {
                head_reduction
                .covering_ty(&old_head)
                .pi_eq_arg_injective()
                .transport(&tail)
            };

            new_head.pair(&head_tag, new_tail_ty.unbind(), &tail)
        });

        /*
        let covering_ty = var_ty.scope(&var_tag, |old_pair| {
            let old_head = old_pair.proj_head();
            let tail = old_pair.proj_tail();

            head_reduction
            .covering_ty(&old_head)
            .pi_eq_cong(
                |old_tail_ty, _, old_body_ty, new_body_ty, pi_tys_eq| {
                    old_tail_ty
                    .pi(&var_tag, |old_tail| {
                        old_body_ty
                        .app(&old_tail)
                        .equals(
                            &new_body_ty
                            .app(
                                &pi_tys_eq
                                .pi_eq_arg_injective()
                                .transport(&old_tail)
                            )
                        )
                    })
                },
                |tail_ty, body_ty| {
                    tail_ty
                    .func(&var_tag, |tail| {
                        body_ty.app(&tail).refl()
                    })
                },
            )
            .app(&tail)
        });

        let covering = var_ty.scope(&var_tag, |old_pair| {
            let old_head = old_pair.proj_head();
            let tail = old_pair.proj_tail();

            head_reduction
            .covering_ty(&old_head)
            .pi_eq_cong(
                |old_tail_ty, new_tail_ty, old_body_ty, new_body_ty, pi_tys_eq| {
                    old_tail_ty
                    .pi(|old_tail| old_body_ty.app(&old_tail).to_ty())
                    .pi(|old_body| {
                        new_tail_ty
                        .weaken_into(&old_body.ctx())
                        .pi(|new_tail| new_body_ty.app(&new_tail).to_ty())
                        .pi(|new_body| {
                            pi_tys_eq
                            .heterogeneous_equal(&old_body, &new_body)
                            .pi(|body_eq| {
                                old_tail_ty
                                .weaken_into(&body_eq.ctx())
                                .pi(|old_tail| {
                                    pi_tys_eq
                                    .weaken_into(&old_tail.ctx())
                                    .pi_eq_cong(
                                        |old_tail_ty, _, old_body_ty, new_body_ty, pi_tys_eq| {
                                            old_tail_ty
                                            .pi(|old_tail| {
                                                old_body_ty
                                                .app(&old_tail)
                                                .equals(
                                                    &new_body_ty
                                                    .app(
                                                        &pi_tys_eq
                                                        .pi_eq_arg_injective()
                                                        .transport(&old_tail)
                                                    )
                                                )
                                            })
                                        },
                                        |tail_ty, body_ty| {
                                            tail_ty
                                            .func(|tail| {
                                                body_ty.app(&tail).refl()
                                            })
                                        },
                                    )
                                    .app(&old_tail)
                                    .heterogeneous_equal(
                                        &old_body.app(&old_tail),
                                        &new_body.app(
                                            &pi_tys_eq
                                            .pi_eq_arg_injective()
                                            .transport(&old_tail)
                                        ),
                                    )
                                })
                            })
                        })
                    })
                },
                |tail_ty, body_ty| {
                    tail_ty
                    .pi(|tail| body_ty.app(&tail).to_ty())
                    .func(|old_body| {
                        tail_ty
                        .weaken_into(&old_body.ctx())
                        .pi(|tail| body_ty.app(&tail).to_ty())
                        .func(|new_body| {
                            old_body
                            .equals(&new_body)
                            .func(|body_eq| {
                                tail_ty
                                .weaken_into(&body_eq.ctx())
                                .func(|tail| {
                                    body_eq
                                    .weaken_into(&tail.ctx())
                                    .map_eq(|body| body.app(&tail))
                                })
                            })
                        })
                    })
                },
            )
            .app(
                &tail_ty
                .bind(&old_head)
                .func(|old_tail| {
                    self.bind(&old_head.pair(tail_ty.unbind(), &old_tail))
                })
            )
            .app(
                &tail_ty
                .bind(&head_reduction.fwd(&head_reduction.rev(&old_head)))
                .func(|new_tail| {
                    self
                    .bind(
                        &head_reduction
                        .fwd(&head_reduction.rev(&old_head))
                        .pair(tail_ty.unbind(), &new_tail)
                    )
                })
            )
            .app(&head_reduction.covering(&old_head))
            .app(&tail)
        });

        self.reduction(
            &new_var_ty, fwd.unbind(), rev.unbind(), covering_ty.unbind(), covering.unbind(),
        )
        */
        todo!()
    }

    fn reduce_constraint_sigma_tail(&self, recursion_depth: u32) -> Reduction {
        /*
        let old_tail_ty = self.var_ty().unwrap_sigma();

        let head_ty = old_tail_ty.var_ty();
        let tail_reduction = head_ty.scope(|head| {
            old_tail_ty
            .bind(&head)
            .scope(|tail| {
                self.bind(&head.pair(old_tail_ty.unbind(), &tail))
            })
            .reduce_constraint(recursion_depth)
        });

        let new_tail_ty = {
            tail_reduction
            .map(|_, tail_reduction| tail_reduction.new_var_ty())
        };

        let new_var_ty = new_tail_ty.to_sigma();

        let fwd = new_var_ty.scope(|new_pair| {
            let head = new_pair.proj_head();
            let new_tail = new_pair.proj_tail();

            let tail_reduction = tail_reduction.bind(&head);
            let old_tail = tail_reduction.fwd(&new_tail);
            head.pair(old_tail_ty.unbind(), &old_tail)
        });

        let rev = self.var_ty().scope(|old_pair| {
            let head = old_pair.proj_head();
            let old_tail = old_pair.proj_tail();
            let tail_reduction = tail_reduction.bind(&head);
            let new_tail = tail_reduction.rev(&old_tail);
            head.pair(new_tail_ty.unbind(), &new_tail)
        });

        let covering_ty = self.var_ty().scope(|old_pair| {
            let head = old_pair.proj_head();
            let old_tail = old_pair.proj_tail();
            let tail_reduction = tail_reduction.bind(&head);
            tail_reduction.covering_ty(&old_tail)
        });

        let covering = self.var_ty().scope(|old_pair| {
            let head = old_pair.proj_head();
            let old_tail = old_pair.proj_tail();
            let tail_reduction = tail_reduction.bind(&head);
            tail_reduction.covering(&old_tail)
        });

        self.reduction(
            &new_var_ty, fwd.unbind(), rev.unbind(), covering_ty.unbind(), covering.unbind(),
        )
        */
        todo!()
    }
    */

    fn reduce_sigma_never_head(&self) -> Reduction {
        let tail_ty = self.var_ty().unwrap_sigma();
        let head_tag = tail_ty.var_tag();
        self.reduce_over_iso(
            &Iso::sigma_never_head_annihilate(&tail_ty),
        )
    }

    fn reduce_sigma_never_tail(&self) -> Reduction {
        self.reduce_impossible(|pair| {
            pair.proj_tail()
        })
    }

    fn reduce_sigma_unit_tail(&self) -> Reduction {
        /*
        Reduction::from_core(
            self
            .core_ref()
            .reduce_strip_tag()
        )
        let tail_ty = self.var_ty().unwrap_sigma();
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
        */
        todo!()
    }

    /*
    fn reduce_sigma_unit_head(&self) -> Reduction {
        /*
        let tail_ty = self.var_ty().unwrap_sigma();
        let (tag, _) = tail_ty.var_ty().unwrap_tagged();

        let new_var_ty = tail_ty.bind(&self.ctx().unit_term().tag(&tag));
        let fwd = new_var_ty.scope(|tail| {
            tail
            .ctx()
            .unit_term()
            .tag(&tag)
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
        */
        todo!()
    }

    fn reduce_sigma_sum_head_distribute(&self) -> Reduction {
        /*
        let tail_ty = self.var_ty().unwrap_sigma();
        let tagged_head_ty = tail_ty.var_ty();
        let (head_tag, head_ty) = tagged_head_ty.unwrap_tagged();
        let (tagged_lhs_ty, rhs_ty) = head_ty.unwrap_sum();
        let (lhs_tag, lhs_ty) = tagged_lhs_ty.unwrap_tagged();

        let new_var_ty = Ty::sum(
            &lhs_ty
            .tag(&head_tag)
            .sigma(|lhs| {
                tail_ty
                .bind(
                    &lhs
                    .strip_tag()
                    .tag(&lhs_tag)
                    .inj_lhs(&rhs_ty)
                    .tag(&head_tag),
                )
            })
            .tag(&lhs_tag),
            &rhs_ty
            .tag(&head_tag)
            .sigma(|rhs| {
                tail_ty
                .bind(
                    &rhs
                    .strip_tag()
                    .inj_rhs(&tagged_lhs_ty)
                    .tag(&head_tag),
                )
            })
        );
        let fwd = new_var_ty.scope(|sum_pair| {
            sum_pair
            .case(
                |_| self.var_ty(),
                |lhs_pair| {
                    lhs_pair
                    .strip_tag()
                    .proj_head()
                    .strip_tag()
                    .tag(&lhs_tag)
                    .inj_lhs(&rhs_ty)
                    .tag(&head_tag)
                    .pair(tail_ty.unbind(), &lhs_pair.strip_tag().proj_tail())
                },
                |rhs_pair| {
                    rhs_pair
                    .proj_head()
                    .strip_tag()
                    .inj_rhs(&tagged_lhs_ty)
                    .tag(&head_tag)
                    .pair(tail_ty.unbind(), &rhs_pair.proj_tail())
                },
            )
        });
        let rev = self.var_ty().scope(|pair| {
            pair
            .proj_head()
            .strip_tag()
            .case(
                |sum| {
                    tail_ty
                    .bind(&sum.tag(&head_tag))
                    .pi(|_| new_var_ty.clone())
                },
                |tagged_lhs| {
                    tail_ty
                    .bind(&tagged_lhs.inj_lhs(&rhs_ty).tag(&head_tag))
                    .func(|tail| {
                        tagged_lhs
                        .weaken_into(&tail.ctx())
                        .strip_tag()
                        .tag(&head_tag)
                        .pair(
                            |lhs| {
                                tail_ty
                                .bind(
                                    &lhs
                                    .strip_tag()
                                    .tag(&lhs_tag)
                                    .inj_lhs(&rhs_ty)
                                    .tag(&head_tag)
                                )
                            },
                            &tail,
                        )
                        .tag(&lhs_tag)
                        .inj_lhs(
                            &rhs_ty
                            .tag(&head_tag)
                            .sigma(|rhs| {
                                tail_ty
                                .bind(&rhs.inj_rhs(&tagged_lhs_ty).tag(&head_tag))
                            })
                        )
                    })
                },
                |rhs| {
                    tail_ty
                    .bind(&rhs.inj_rhs(&tagged_lhs_ty).tag(&head_tag))
                    .func(|tail| {
                        rhs
                        .weaken_into(&tail.ctx())
                        .tag(&head_tag)
                        .pair(
                            |rhs| {
                                tail_ty
                                .bind(
                                    &rhs
                                    .strip_tag()
                                    .inj_rhs(&tagged_lhs_ty)
                                    .tag(&head_tag),
                                )
                            },
                            &tail,
                        )
                        .inj_rhs(
                            &lhs_ty
                            .tag(&head_tag)
                            .sigma(|lhs| {
                                tail_ty
                                .bind(
                                    &lhs
                                    .strip_tag()
                                    .tag(&lhs_tag)
                                    .inj_lhs(&rhs_ty)
                                    .tag(&head_tag)
                                )
                            })
                        )
                    })
                },
            )
            .app(&pair.proj_tail())
        });
        let covering_ty = self.var_ty().scope(|pair| {
            pair
            .proj_head()
            .strip_tag()
            .case(
                |sum| {
                    tail_ty
                    .bind(&sum.tag(&head_tag))
                    .pi(|tail| {
                        let pair = {
                            sum
                            .weaken_into(&tail.ctx())
                            .tag(&head_tag)
                            .pair(tail_ty.unbind(), &tail)
                        };

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
                    let sum = lhs.inj_lhs(&rhs_ty).tag(&head_tag);

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
                    let sum = rhs.inj_rhs(&tagged_lhs_ty).tag(&head_tag);

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
            .strip_tag()
            .case(
                |sum| {
                    let sum = sum.tag(&head_tag);

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
                    let sum = lhs.inj_lhs(&rhs_ty).tag(&head_tag);

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
                    let sum = rhs.inj_rhs(&tagged_lhs_ty).tag(&head_tag);

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
        */
        todo!()
    }

    fn reduce_sigma_reassociate_to_tail(&self) -> Reduction {
        /*
        let old_tail_ty = self.var_ty().unwrap_sigma();
        let tagged_old_head_middle_ty = old_tail_ty.var_ty();
        let (outer_tag, old_head_middle_ty) = tagged_old_head_middle_ty.unwrap_tagged();
        let middle_ty = old_head_middle_ty.unwrap_sigma();

        let new_tail_ty = {
            middle_ty
            .map(|tagged_head, bound_middle_ty| {
                bound_middle_ty
                .tag(&outer_tag)
                .scope(|tagged_middle| {
                    old_tail_ty
                    .bind(
                        &tagged_head
                        .pair(middle_ty.unbind(), &tagged_middle.strip_tag())
                        .tag(&outer_tag)
                    )
                })
            })
        };

        let new_var_ty = new_tail_ty.map(|_, tail_ty| tail_ty.to_sigma()).to_sigma();

        let fwd = new_var_ty.scope(|pair| {
            let head = pair.proj_head();
            let middle_tail = pair.proj_tail();
            let middle = middle_tail.proj_head();
            let tail = middle_tail.proj_tail();

            head
            .pair(middle_ty.unbind(), &middle.strip_tag())
            .pair(old_tail_ty.unbind(), &tail)
        });
        let rev = self.var_ty().scope(|pair| {
            let head_middle = pair.proj_head().strip_tag();
            let head = head_middle.proj_head();
            let middle = head_middle.proj_tail();
            let tail = pair.proj_tail();

            head
            .pair(
                |head| new_tail_ty.bind(&head).to_sigma(),
                &middle
                .pair(
                    |middle| new_tail_ty.bind(&head).bind(&middle),
                    &tail,
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
        */
        todo!()
    }

    fn reduce_sigma_constrained(
        &self,
        head: &Tm,
        proof: &Scope<Scope<Tm>>,
    ) -> Reduction {
        /*
        let old_tail_ty = self.var_ty().unwrap_sigma();

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
        */
        todo!()
    }

    fn reduce_sigma(
        &self,
        head_reduction: &Reduction,
        tail_reduction: &Scope<Reduction>,
    ) -> Reduction {
        /*
        let tail_ty = tail_reduction.map(|_, tail_reduction| tail_reduction.old_var_ty());

        let new_var_ty = {
            head_reduction
            .new_var_ty()
            .sigma(|new_head| {
                tail_reduction
                .bind(&head_reduction.fwd(&new_head))
                .new_var_ty()
            })
        };
        
        let fwd = {
            new_var_ty
            .scope(|new_pair| {
                let new_head = new_pair.proj_head();
                let new_tail = new_pair.proj_tail();

                let old_head = head_reduction.fwd(&new_head);
                let old_tail = tail_reduction.bind(&old_head).fwd(&new_tail);
                
                old_head.pair(tail_ty.unbind(), &old_tail)
            })
        };

        let rev = {
            self
            .var_ty()
            .scope(|old_pair| {
                let old_head = old_pair.proj_head();
                let old_tail = old_pair.proj_tail();

                let new_head = head_reduction.rev(&old_head);
                let new_tail = tail_reduction.bind(&old_head).rev(&old_tail);

                let new_tail = {
                    head_reduction
                    .covering_ty(&old_head)
                    .pi_eq_arg_injective()
                    .transport(&new_tail)
                };

                new_head
                .pair(
                    |new_head| {
                        tail_reduction
                        .bind(&head_reduction.fwd(&new_head))
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
                .covering_ty(&old_head)
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
                .app(&tail_reduction.rev(&old_tail))
                .app(
                    &self
                    .bind(&old_pair)
                    .ty()
                    .to_term()
                )
                .app(&tail_reduction.covering_ty(&old_tail))
            })
        };

        let covering = {
            self
            .var_ty()
            .scope(|old_pair| {
                let old_head = old_pair.proj_head();
                let old_tail = old_pair.proj_tail();

                let new_head = head_reduction.rev(&old_head);
                let round_trip_head = head_reduction.fwd(&new_head);

                let round_trip_tail_reduced = tail_reduction.bind(&round_trip_head);
                let tail_reduction = tail_reduction.bind(&old_head);

                head_reduction
                .covering_ty(&old_head)
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
                .app(&tail_reduction.rev(&old_tail))
                .app(
                    &self
                    .bind(&old_pair)
                    .ty()
                    .to_term(),
                )
                .app(&tail_reduction.covering_ty(&old_tail))
                .app(
                    &tail_reduction
                    .new_var_ty()
                    .func(|new_tail| {
                        self
                        .bind(
                            &old_head
                            .pair(tail_ty.unbind(), &tail_reduction.fwd(&new_tail))
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
                            .pair(tail_ty.unbind(), &round_trip_tail_reduced.fwd(&new_tail))
                        )
                    })
                )
                .app(&head_reduction.covering(&old_head))
                .app(&self.bind(&old_pair))
                .app(&tail_reduction.covering(&old_tail))
            })
        };

        self.reduction(
            &new_var_ty,
            fwd.unbind(),
            rev.unbind(),
            covering_ty.unbind(),
            covering.unbind(),
        )
        */
        todo!()
    }
    */
}

