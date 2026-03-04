use crate::priv_prelude::*;

impl InferScope<Tm> {
    pub(crate) fn reduce_constraint_sigma(&self, recursion_depth: u32) -> Reduction {
        let mut recursion_depth = recursion_depth;

        let mut reduction = self.reduce_constraint_sigma_tail(recursion_depth);
        if let Some(reduction) = reduction.try_apply_sigma_tail_identities() {
            return reduction.reduce_more(recursion_depth);
        }

        loop {
            let constraint_ty_before = reduction.new_constraint_ty();
            reduction = {
                reduction
                .and_then(|scope| scope.reduce_constraint_sigma_head(recursion_depth))
            };
            let constraint_ty_after = reduction.new_constraint_ty();
            let (new_head_name, tail_ty) = reduction.new_constraint_ty().unwrap_sigma();

            if let Some(reduction) = reduction.try_apply_sigma_head_identities() {
                return reduction.reduce_more(recursion_depth);
            }

            let constraint_name = reduction.new_constraint_name();
            if let Some((head, proof)) = tail_ty.constrains_own_var(&constraint_name) {
                return {
                    reduction
                    .and_then(|scope| {
                        scope.reduce_over_iso(
                            &Iso::sigma_tail_ty_constrains_head_ty(
                                &new_head_name,
                                tail_ty.unbind(),
                                &head,
                                |head, tail| proof.bind(&head).bind(&tail),
                                &constraint_name,
                            ),
                            &constraint_name,
                        )
                    })
                    .reduce_more(recursion_depth)
                };
            }

            if constraint_ty_before == constraint_ty_after {
                if tail_ty.var_eliminated() {
                    if let Some(reduction) = reduction.try_apply_sigma_head_distributivity() {
                        return reduction.reduce_more(recursion_depth);
                    }
                }

                return reduction;
            }
            let Some(next_recursion_depth) = recursion_depth.checked_sub(1) else {
                return reduction;
            };
            recursion_depth = next_recursion_depth;

            let constraint_ty_before = constraint_ty_after;
            reduction = {
                reduction
                .and_then(|scope| scope.reduce_constraint_sigma_tail(recursion_depth))
            };
            let constraint_ty_after = reduction.new_constraint_ty();
            let (_, tail_ty) = constraint_ty_after.unwrap_sigma();

            if let Some(reduction) = reduction.try_apply_sigma_tail_identities() {
                return reduction.reduce_more(recursion_depth);
            }

            if constraint_ty_before == constraint_ty_after {
                if tail_ty.var_eliminated() {
                    if let Some(reduction) = reduction.try_apply_sigma_head_distributivity() {
                        return reduction.reduce_more(recursion_depth);
                    }
                }

                return reduction;
            }
        }
    }

    fn reduce_constraint_sigma_head(&self, recursion_depth: u32) -> Reduction {
        let constraint_name = self.constraint_name();
        let old_constraint_ty = self.constraint_ty();
        let body = self.body();
        let (old_head_name, tail_ty) = old_constraint_ty.unwrap_sigma();
        let old_head_ty = tail_ty.var_ty();

        let head_reduction = {
            InferScope::from_scope(
                &old_head_name,
                &old_head_ty
                .scope(|old_head| {
                    tail_ty
                    .bind(&old_head)
                    .func(&constraint_name, |tail| {
                        body
                        .bind(&old_head.pair(&old_head_name, tail_ty.unbind(), &tail))
                    })
                })
            )
            .reduce_constraint(recursion_depth)
        };

        let new_head_name = head_reduction.new_constraint_name();
        let new_head_ty = head_reduction.new_constraint_ty();
        let new_tail_ty = new_head_ty.scope(|new_head| {
            tail_ty.bind(&head_reduction.fwd(&new_head))
        });
        let new_constraint_ty = new_tail_ty.to_sigma(&new_head_name);

        let fwd = new_constraint_ty.scope(|new_pair| {
            let new_head = new_pair.proj_head();
            let tail = new_pair.proj_tail();

            head_reduction
            .fwd(&new_head)
            .pair(&old_head_name, tail_ty.unbind(), &tail)
        });

        let rev = old_constraint_ty.scope(|old_pair| {
            let old_head = old_pair.proj_head();
            let tail = old_pair.proj_tail();

            let new_head = head_reduction.rev(&old_head);
            let tail = {
                head_reduction
                .covering_ty(&old_head)
                .pi_eq_arg_injective()
                .transport(&tail)
            };

            new_head.pair(&new_head_name, new_tail_ty.unbind(), &tail)
        });

        let covering_ty = old_constraint_ty.scope(|old_pair| {
            let old_head = old_pair.proj_head();
            let tail = old_pair.proj_tail();

            head_reduction
            .covering_ty(&old_head)
            .pi_eq_cong(
                |
                    old_constraint_name,
                    _new_constraint_name,
                    old_tail_ty,
                    _new_tail_ty,
                    old_body_ty,
                    new_body_ty,
                    pi_eq,
                | {
                    old_tail_ty
                    .pi(&old_constraint_name, |old_tail| {
                        old_body_ty
                        .app(&old_tail)
                        .equals(
                            &new_body_ty
                            .app(
                                &pi_eq
                                .pi_eq_arg_injective()
                                .transport(&old_tail)
                            )
                        )
                    })
                },
                |constraint_name, tail_ty, body_ty| {
                    tail_ty
                    .func(&constraint_name, |tail| {
                        body_ty.app(&tail).refl()
                    })
                },
            )
            .app(&tail)
        });

        let covering = old_constraint_ty.scope(|old_pair| {
            let old_head = old_pair.proj_head();
            let tail = old_pair.proj_tail();

            let old_body_name = TagScheme::name_from_str("old_body");
            let new_body_name = TagScheme::name_from_str("old_body");
            let body_eq_name = TagScheme::name_from_str("body_eq");

            head_reduction
            .covering_ty(&old_head)
            .pi_eq_cong(
                |
                    old_constraint_name,
                    new_constraint_name,
                    old_tail_ty,
                    new_tail_ty,
                    old_body_ty,
                    new_body_ty,
                    pi_eq,
                | {
                    old_tail_ty
                    .pi(&old_constraint_name, |old_tail| old_body_ty.app(&old_tail).to_ty())
                    .pi(&old_body_name, |old_body| {
                        new_tail_ty
                        .weaken_into(&old_body.ctx())
                        .pi(&new_constraint_name, |new_tail| new_body_ty.app(&new_tail).to_ty())
                        .pi(&new_body_name, |new_body| {
                            pi_eq
                            .heterogeneous_equal(&old_body, &new_body)
                            .pi(&body_eq_name, |body_eq| {
                                old_tail_ty
                                .weaken_into(&body_eq.ctx())
                                .pi(&old_constraint_name, |old_tail| {
                                    pi_eq
                                    .weaken_into(&old_tail.ctx())
                                    .pi_eq_cong(
                                        |
                                            old_constraint_name,
                                            _new_constraint_name,
                                            old_tail_ty,
                                            _new_tail_ty,
                                            old_body_ty,
                                            new_body_ty,
                                            pi_eq,
                                        | {
                                            old_tail_ty
                                            .pi(&old_constraint_name, |old_tail| {
                                                old_body_ty
                                                .app(&old_tail)
                                                .equals(
                                                    &new_body_ty
                                                    .app(
                                                        &pi_eq
                                                        .pi_eq_arg_injective()
                                                        .transport(&old_tail)
                                                    )
                                                )
                                            })
                                        },
                                        |constraint_name, tail_ty, body_ty| {
                                            tail_ty
                                            .func(&constraint_name, |tail| {
                                                body_ty.app(&tail).refl()
                                            })
                                        },
                                    )
                                    .app(&old_tail)
                                    .heterogeneous_equal(
                                        &old_body.app(&old_tail),
                                        &new_body.app(
                                            &pi_eq
                                            .pi_eq_arg_injective()
                                            .transport(&old_tail)
                                        ),
                                    )
                                })
                            })
                        })
                    })
                },
                |constraint_name, tail_ty, body_ty| {
                    tail_ty
                    .pi(&constraint_name, |tail| body_ty.app(&tail).to_ty())
                    .func(&old_body_name, |old_body| {
                        tail_ty
                        .weaken_into(&old_body.ctx())
                        .pi(&constraint_name, |tail| body_ty.app(&tail).to_ty())
                        .func(&new_body_name, |new_body| {
                            old_body
                            .equals(&new_body)
                            .func(&body_eq_name, |body_eq| {
                                tail_ty
                                .weaken_into(&body_eq.ctx())
                                .func(&constraint_name, |tail| {
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
                .func(&constraint_name, |old_tail| {
                    body.bind(&old_head.pair(&old_head_name, tail_ty.unbind(), &old_tail))
                })
            )
            .app(
                &tail_ty
                .bind(&head_reduction.fwd(&head_reduction.rev(&old_head)))
                .func(&constraint_name, |new_tail| {
                    body
                    .bind(
                        &head_reduction
                        .fwd(&head_reduction.rev(&old_head))
                        .pair(&old_head_name, tail_ty.unbind(), &new_tail)
                    )
                })
            )
            .app(&head_reduction.covering(&old_head))
            .app(&tail)
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

    fn reduce_constraint_sigma_tail(&self, recursion_depth: u32) -> Reduction {
        let old_constraint_name = self.constraint_name();
        let old_constraint_ty = self.constraint_ty();
        let (head_name, old_tail_ty) = old_constraint_ty.unwrap_sigma();
        let body = self.body();
        let head_ty = old_tail_ty.var_ty();

        let tail_reduction = head_ty.scope(|head| {
            InferScope::from_scope(
                &old_constraint_name,
                &old_tail_ty
                .bind(&head)
                .scope(|tail| {
                    body.bind(&head.pair(&head_name, old_tail_ty.unbind(), &tail))
                }),
            )
            .reduce_constraint(recursion_depth)
        });

        let new_constraint_name = {
            tail_reduction
            .map(|_, tail_reduction| tail_reduction.new_constraint_name())
            .try_strengthen()
            .unwrap_or_else(|| old_constraint_name.clone())
        };
        let new_tail_ty = {
            tail_reduction
            .map(|_, tail_reduction| tail_reduction.new_constraint_ty())
        };

        let new_constraint_ty = new_tail_ty.to_sigma(&head_name);

        let fwd = new_constraint_ty.scope(|new_pair| {
            let head = new_pair.proj_head();
            let new_tail = new_pair.proj_tail();

            let tail_reduction = tail_reduction.bind(&head);
            let old_tail = tail_reduction.fwd(&new_tail);
            head.pair(&head_name, old_tail_ty.unbind(), &old_tail)
        });

        let rev = old_constraint_ty.scope(|old_pair| {
            let head = old_pair.proj_head();
            let old_tail = old_pair.proj_tail();
            let tail_reduction = tail_reduction.bind(&head);
            let new_tail = tail_reduction.rev(&old_tail);
            head.pair(&head_name, new_tail_ty.unbind(), &new_tail)
        });

        let covering_ty = old_constraint_ty.scope(|old_pair| {
            let head = old_pair.proj_head();
            let old_tail = old_pair.proj_tail();
            let tail_reduction = tail_reduction.bind(&head);
            tail_reduction.covering_ty(&old_tail)
        });

        let covering = old_constraint_ty.scope(|old_pair| {
            let head = old_pair.proj_head();
            let old_tail = old_pair.proj_tail();
            let tail_reduction = tail_reduction.bind(&head);
            tail_reduction.covering(&old_tail)
        });

        Reduction::new(
            &old_constraint_name,
            &new_constraint_name,
            &body,
            &new_constraint_ty,
            fwd.unbind(),
            rev.unbind(),
            covering_ty.unbind(),
            covering.unbind(),
        )
    }
}

impl Reduction {
    fn try_apply_sigma_head_identities(&self) -> Option<Reduction> {
        let constraint_name = self.new_constraint_name();
        let constraint_ty = self.new_constraint_ty();
        let (head_name, tail_ty) = constraint_ty.unwrap_sigma();
        let head_ty = tail_ty.var_ty();

        match head_ty.kind() {
            TyKind::Never => {
                return Some(self.and_then(|scope| {
                    scope
                    .reduce_over_iso(
                        &Iso::sigma_never_head(&head_name, tail_ty.unbind()),
                        &head_name,
                    )
                }));
            },
            TyKind::Unit => {
                return Some(self.and_then(|scope| {
                    scope.reduce_over_iso(
                        &Iso::sigma_unit_head(&head_name, tail_ty.unbind()),
                        &constraint_name,
                    )
                }));
            },
            _ => None,
        }
    }

    fn try_apply_sigma_tail_identities(&self) -> Option<Reduction> {
        let constraint_name = self.new_constraint_name();
        let constraint_ty = self.new_constraint_ty();
        let (head_name, tail_ty) = constraint_ty.unwrap_sigma();
        let head_ty = tail_ty.var_ty();

        match tail_ty.map_out(|_, tail_ty| tail_ty.kind()) {
            TyKind::Never => {
                return Some(self.and_then(|scope| {
                    scope.reduce_over_iso(
                        &Iso::sigma_never_tail(&head_name, &head_ty),
                        &constraint_name,
                    )
                }));
            },
            TyKind::Unit => {
                return Some(self.and_then(|scope| {
                    scope
                    .reduce_over_iso(
                        &Iso::sigma_unit_tail(&head_name, &head_ty),
                        &head_name,
                    )
                }));
            },
            _ => None,
        }
    }

    fn try_apply_sigma_head_distributivity(&self) -> Option<Reduction> {
        let constraint_name = self.new_constraint_name();
        let constraint_ty = self.new_constraint_ty();
        let (head_name, tail_ty) = constraint_ty.unwrap_sigma();
        let head_ty = tail_ty.var_ty();

        match head_ty.kind() {
            TyKind::Nat => {
                return Some(
                    self.and_then(|scope| {
                        scope.reduce_over_iso(
                            &Iso::sigma_head_congruence(
                                &head_name,
                                &head_name,
                                &Iso::nat_is_zero_or_succ(&scope.ctx()),
                                tail_ty.unbind(),
                                &constraint_name,
                            ),
                            &constraint_name,
                        )
                    })
                );
            },
            TyKind::Sum { lhs_name, lhs_ty, rhs_ty } => {
                return Some(
                    self.and_then(|scope| {
                        scope.reduce_over_iso(
                            &Iso::sigma_sum_head_distribute(
                                &head_name,
                                &lhs_name,
                                &lhs_ty,
                                &rhs_ty,
                                tail_ty.unbind(),
                            ),
                            &constraint_name,
                        )
                    })
                );
            },
            TyKind::Sigma { head_name: head_head_name, tail_ty: head_tail_ty } => {
                let head_head_ty = head_tail_ty.var_ty();
                return Some(
                    self.and_then(|scope| {
                        scope.reduce_over_iso(
                            &Iso::sigma_reassociate_to_tail(
                                &head_name,
                                &head_head_name,
                                &head_head_ty,
                                head_tail_ty.unbind(),
                                tail_ty.unbind(),
                            ),
                            &constraint_name,
                        )
                    })
                );
            },
            _ => None,
        }
    }
}

