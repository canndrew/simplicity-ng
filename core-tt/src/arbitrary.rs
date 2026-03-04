use crate::priv_prelude::*;

// FIXME: hack to prevent stack overflows until they're fixed.
const MAX_DEPTH: usize = 10;

impl<'a, S> Arbitrary<'a> for Ctx<S>
where
    S: Scheme,
    S::Tag: Arbitrary<'a>,
{
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Ctx<S>> {
        let depth = u.len() / 8;
        arbitrary_ctx_with_depth(depth, u)
    }

    /*
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        Self::try_size_hint(depth).unwrap_or_default()
    }

    fn try_size_hint(depth: usize) -> Result<(usize, Option<usize>), MaxRecursionReached> {

    }
    */
}

impl<'a, S> Arbitrary<'a> for Ty<S>
where
    S: Scheme,
    S::Tag: Arbitrary<'a>,
{
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Ty<S>> {
        let depth = u.len() / 7;
        let ctx = arbitrary_ctx_with_depth(depth.saturating_sub(2), u)?;
        arbitrary_ty_under_ctx_with_depth(&ctx, depth.saturating_sub(2), u)
    }
}

impl<'a, S> Arbitrary<'a> for Tm<S>
where
    S: Scheme,
    S::Tag: Arbitrary<'a>,
{
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Tm<S>> {
        let depth = u.len() / 8;
        let ctx = arbitrary_ctx_with_depth(depth.saturating_sub(2), u)?;
        arbitrary_term_under_ctx_with_depth(&ctx, depth.saturating_sub(2), u)
    }
}

impl<'a, S> Arbitrary<'a> for Stuck<S>
where
    S: Scheme,
    S::Tag: Arbitrary<'a>,
{
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Stuck<S>> {
        let depth = u.len() / 8;
        let ctx = arbitrary_ctx_with_depth(depth.saturating_sub(2), u)?;
        arbitrary_stuck_under_ctx_with_depth(&ctx, depth.saturating_sub(2), u)
    }
}

impl<'a, S> Arbitrary<'a> for Name<S>
where
    S: Scheme,
    S::Tag: Arbitrary<'a>,
{
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Name<S>> {
        let depth = u.len() / 8;
        let ctx = arbitrary_ctx_with_depth(depth.saturating_sub(2), u)?;
        arbitrary_name_under_ctx_with_depth(&ctx, depth.saturating_sub(2), u)
    }
}

type Choice<'c, 'a, T> = Box<dyn Fn(&mut Unstructured<'a>) -> arbitrary::Result<T> + 'c>;

pub fn arbitrary_ctx<'a, S>(
    u: &mut Unstructured<'a>,
) -> arbitrary::Result<Ctx<S>>
where
    S: Scheme,
    S::Tag: Arbitrary<'a>,
{
    let depth = u.len() / 8;
    arbitrary_ctx_with_depth(depth, u)
}

pub fn arbitrary_ty_under_ctx<'a, S>(
    ctx: &Ctx<S>,
    u: &mut Unstructured<'a>,
) -> arbitrary::Result<Ty<S>>
where
    S: Scheme,
    S::Tag: Arbitrary<'a>,
{
    let depth = u.len() / 5;
    arbitrary_ty_under_ctx_with_depth(&ctx, depth, u)
}

pub fn arbitrary_term_under_ctx<'a, S>(
    ctx: &Ctx<S>,
    u: &mut Unstructured<'a>,
) -> arbitrary::Result<Tm<S>>
where
    S: Scheme,
    S::Tag: Arbitrary<'a>,
{
    let depth = u.len() / 6;
    arbitrary_term_under_ctx_with_depth(&ctx, depth, u)
}

pub fn arbitrary_term_of_ty<'a, S>(
    ty: &Ty<S>,
    u: &mut Unstructured<'a>,
) -> arbitrary::Result<Tm<S>>
where
    S: Scheme,
    S::Tag: Arbitrary<'a>,
{
    let depth = u.len() / 3;
    arbitrary_term_of_ty_with_depth(&ty, depth, u)
}

pub fn arbitrary_stuck_under_ctx<'a, S>(
    ctx: &Ctx<S>,
    u: &mut Unstructured<'a>,
) -> arbitrary::Result<Stuck<S>>
where
    S: Scheme,
    S::Tag: Arbitrary<'a>,
{
    let depth = u.len() / 4;
    arbitrary_stuck_under_ctx_with_depth(&ctx, depth, u)
}

pub fn arbitrary_name_under_ctx<'a, S>(
    ctx: &Ctx<S>,
    u: &mut Unstructured<'a>,
) -> arbitrary::Result<Name<S>>
where
    S: Scheme,
    S::Tag: Arbitrary<'a>,
{
    let depth = u.len() / 5;
    arbitrary_name_under_ctx_with_depth(&ctx, depth, u)
}

fn arbitrary_ctx_with_depth<'a, S>(
    depth: usize,
    u: &mut Unstructured<'a>,
) -> arbitrary::Result<Ctx<S>>
where
    S: Scheme,
    S::Tag: Arbitrary<'a>,
{
    // hack. prevent stack overflows until they're fixed.
    let depth = std::cmp::min(depth, MAX_DEPTH);

    if u.ratio(1, 1 + depth / 2)? {
        Ok(Ctx::root())
    } else {
        let ctx = arbitrary_ctx_with_depth(depth.saturating_sub(2), u)?;
        let ty = arbitrary_ty_under_ctx_with_depth(&ctx, depth.saturating_sub(2), u)?;
        Ok(ctx.cons(&ty))
    }
}

fn arbitrary_ty_under_ctx_with_depth<'a, S>(
    ctx: &Ctx<S>,
    depth: usize,
    u: &mut Unstructured<'a>,
) -> arbitrary::Result<Ty<S>>
where
    S: Scheme,
    S::Tag: Arbitrary<'a>,
{
    // hack. prevent stack overflows until they're fixed.
    let depth = std::cmp::min(depth, MAX_DEPTH);

    let mut choices: Vec<Choice<'_, 'a, Ty<S>>> = Vec::new();
    choices.push(Box::new(move |_u| Ok(ctx.universe())));
    choices.push(Box::new(move |_u| Ok(ctx.nat())));
    choices.push(Box::new(move |_u| Ok(ctx.never())));
    choices.push(Box::new(move |_u| Ok(ctx.unit_ty())));
    if let Some(depth) = depth.checked_sub(2) {
        choices.push(Box::new(move |u| {
            let mut eq_term_0 = arbitrary_term_under_ctx_with_depth(ctx, depth, u)?;
            let mut eq_term_1 = arbitrary_term_of_ty_with_depth(&eq_term_0.ty(), depth, u)?;
            if u.arbitrary()? {
                mem::swap(&mut eq_term_0, &mut eq_term_1);
            }
            Ok(eq_term_0.equals(&eq_term_1))
        }));
        choices.push(Box::new(move |u| {
            let lhs_name = arbitrary_name_under_ctx_with_depth(ctx, depth, u)?;
            let lhs_ty = arbitrary_ty_under_ctx_with_depth(ctx, depth, u)?;
            let rhs_ty = arbitrary_ty_under_ctx_with_depth(ctx, depth, u)?;
            Ok(lhs_ty.sum(&lhs_name, &rhs_ty))
        }));
        choices.push(Box::new(move |u| {
            let head_name = arbitrary_name_under_ctx_with_depth(ctx, depth, u)?;
            let head_ty = arbitrary_ty_under_ctx_with_depth(ctx, depth, u)?;
            let tail_ty = head_ty.try_scope(|head_term| {
                arbitrary_ty_under_ctx_with_depth(&head_term.ctx(), depth, u)
            })?;
            Ok(head_ty.sigma(&head_name, tail_ty.unbind()))
        }));
        choices.push(Box::new(move |u| {
            let arg_name = arbitrary_name_under_ctx_with_depth(ctx, depth, u)?;
            let arg_ty = arbitrary_ty_under_ctx_with_depth(ctx, depth, u)?;
            let res_ty = arg_ty.try_scope(|arg_term| {
                arbitrary_ty_under_ctx_with_depth(&arg_term.ctx(), depth, u)
            })?;
            Ok(arg_ty.pi(&arg_name, res_ty.unbind()))
        }));
    }

    let choice = u.choose_iter(choices.into_iter())?;
    choice(u)
}

fn arbitrary_term_under_ctx_with_depth<'a, S>(
    ctx: &Ctx<S>,
    depth: usize,
    u: &mut Unstructured<'a>,
) -> arbitrary::Result<Tm<S>>
where
    S: Scheme,
    S::Tag: Arbitrary<'a>,
{
    // hack. prevent stack overflows until they're fixed.
    let depth = std::cmp::min(depth, MAX_DEPTH);

    let mut choices: Vec<Choice<'_, 'a, Tm<S>>> = Vec::new();
    choices.push(Box::new(move |_u| Ok(ctx.unit_term())));
    if let Some(depth) = depth.checked_sub(1) {
        for _ in 0..ctx.len() {
            choices.push(Box::new(move |u| {
                let stuck = arbitrary_stuck_under_ctx_with_depth(ctx, depth, u)?;
                Ok(stuck.to_term())
            }));
        }
        choices.push(Box::new(move |u| {
            let ty = arbitrary_ty_under_ctx_with_depth(ctx, depth, u)?;
            Ok(ty.to_term())
        }));
        choices.push(Box::new(move |u| {
            let eq_term = arbitrary_term_under_ctx_with_depth(ctx, depth, u)?;
            Ok(eq_term.refl())
        }));
    }
    if let Some(depth) = depth.checked_sub(2) {
        choices.push(Box::new(move |u| {
            let lhs_name = arbitrary_name_under_ctx_with_depth(ctx, depth, u)?;
            let lhs_term = arbitrary_term_under_ctx_with_depth(ctx, depth, u)?;
            let rhs_ty = arbitrary_ty_under_ctx_with_depth(ctx, depth, u)?;
            Ok(lhs_term.inj_lhs(&lhs_name, &rhs_ty))
        }));
        choices.push(Box::new(move |u| {
            let lhs_name = arbitrary_name_under_ctx_with_depth(ctx, depth, u)?;
            let rhs_term = arbitrary_term_under_ctx_with_depth(ctx, depth, u)?;
            let lhs_ty = arbitrary_ty_under_ctx_with_depth(ctx, depth, u)?;
            Ok(rhs_term.inj_rhs(&lhs_name, &lhs_ty))
        }));
        choices.push(Box::new(move |u| {
            let head_name = arbitrary_name_under_ctx_with_depth(ctx, depth, u)?;
            let head_term = arbitrary_term_under_ctx_with_depth(ctx, depth, u)?;
            let tail_term = head_term.ty().try_scope(|head_term| {
                arbitrary_term_under_ctx_with_depth(&head_term.ctx(), depth, u)
            })?;
            let tail_ty = tail_term.map(|_head_term, term| term.ty());
            let tail_term = tail_term.bind(&head_term);
            Ok(head_term.pair(&head_name, tail_ty.unbind(), &tail_term))
        }));
        choices.push(Box::new(move |u| {
            let arg_name = arbitrary_name_under_ctx_with_depth(ctx, depth, u)?;
            let arg_ty = arbitrary_ty_under_ctx_with_depth(ctx, depth, u)?;
            let res_term = arg_ty.try_scope(|arg_term| {
                arbitrary_term_under_ctx_with_depth(&arg_term.ctx(), depth, u)
            })?;
            Ok(arg_ty.func(&arg_name, res_term.unbind()))
        }));
    }

    let choice = u.choose_iter(choices.into_iter())?;
    choice(u)
}

fn arbitrary_term_of_ty_with_depth<'a, S>(
    ty: &Ty<S>,
    depth: usize,
    u: &mut Unstructured<'a>,
) -> arbitrary::Result<Tm<S>>
where
    S: Scheme,
    S::Tag: Arbitrary<'a>,
{
    // hack. prevent stack overflows until they're fixed.
    let depth = std::cmp::min(depth, MAX_DEPTH);

    let mut valid_indices = Vec::new();
    for index in 0..ty.ctx().len() {
        let var_ty = ty.ctx().get_ty(index);
        if var_ty == *ty {
            valid_indices.push(index);
        }
    }
   
    let index = u.choose_index(valid_indices.len() + 1)?;
    match valid_indices.get(index) {
        Some(index) => {
            Ok(ty.ctx().var(*index))
        },
        None => {
            let term_opt = match ty.kind() {
                TyKind::Stuck { .. } => None,
                TyKind::Name => {
                    if let Some(depth) = depth.checked_sub(1) {
                        let name = arbitrary_name_under_ctx_with_depth(&ty.ctx(), depth, u)?;
                        Some(name.to_term())
                    } else {
                        None
                    }
                },
                TyKind::Universe => {
                    if let Some(depth) = depth.checked_sub(1) {
                        let ty = arbitrary_ty_under_ctx_with_depth(&ty.ctx(), depth, u)?;
                        Some(ty.to_term())
                    } else {
                        None
                    }
                },
                TyKind::Nat => {
                    match depth.checked_sub(1) {
                        None => Some(ty.ctx().zero()),
                        Some(depth) => {
                            if u.arbitrary()? {
                                Some(ty.ctx().zero())
                            } else {
                                let pred_term = arbitrary_term_of_ty_with_depth(&ty, depth / 2, u)?;
                                Some(pred_term.succs(1u32))
                            }
                        },
                    }
                },
                TyKind::Equal { eq_term_0, eq_term_1 } => {
                    as_equal(eq_term_0, eq_term_1).map(|eq_term| eq_term.refl())
                },
                TyKind::Never => None,
                TyKind::Unit => Some(ty.ctx().unit_term()),
                TyKind::Sum { lhs_name, lhs_ty, rhs_ty } => {
                    if let Some(depth) = depth.checked_sub(1) {
                        if u.arbitrary()? {
                            Some(
                                arbitrary_term_of_ty_with_depth(&lhs_ty, depth, u)?
                                .inj_lhs(&lhs_name, &rhs_ty)
                            )
                        } else {
                            Some(
                                arbitrary_term_of_ty_with_depth(&rhs_ty, depth, u)?
                                .inj_rhs(&lhs_name, &lhs_ty)
                            )
                        }
                    } else {
                        None
                    }
                },
                TyKind::Sigma { head_name, tail_ty } => {
                    if let Some(depth) = depth.checked_sub(1) {
                        let head_term = arbitrary_term_of_ty_with_depth(&tail_ty.var_ty(), depth, u)?;
                        let substituted_tail_ty = tail_ty.bind(&head_term);
                        let tail_term = arbitrary_term_of_ty_with_depth(&substituted_tail_ty, depth, u)?;
                        let term = head_term.pair(
                            &head_name,
                            tail_ty.unbind(),
                            &tail_term,
                        );
                        Some(term)
                    } else {
                        None
                    }
                },
                TyKind::Pi { arg_name, res_ty } => {
                    if let Some(depth) = depth.checked_sub(1) {
                        let res_term = res_ty.var_ty().try_scope(|arg_term| {
                            arbitrary_term_of_ty_with_depth(&res_ty.bind(&arg_term), depth, u)
                        })?;
                        Some(res_ty.var_ty().func(&arg_name, res_term.unbind()))
                    } else {
                        None
                    }
                },
            };
            match term_opt {
                Some(term) => Ok(term),
                None => {
                    let index = u.choose_index(valid_indices.len())?;
                    let index = valid_indices[index];
                    Ok(ty.ctx().var(index))
                },
            }
        },
    }
}

fn arbitrary_stuck_under_ctx_with_depth<'a, S>(
    ctx: &Ctx<S>,
    depth: usize,
    u: &mut Unstructured<'a>,
) -> arbitrary::Result<Stuck<S>>
where
    S: Scheme,
    S::Tag: Arbitrary<'a>,
{
    // hack. prevent stack overflows until they're fixed.
    let depth = std::cmp::min(depth, MAX_DEPTH);

    if let Some(depth) = depth.checked_sub(2) && u.arbitrary()? {
        let stuck = arbitrary_stuck_under_ctx_with_depth(ctx, depth, u)?;
        let term = match stuck.ty().kind() {
            TyKind::Stuck { .. } |
            TyKind::Name |
            TyKind::Universe => stuck.to_term(),

            TyKind::Nat => {
                match (u.arbitrary()?, u.arbitrary()?) {
                    (false, false) => {
                        let motive = ctx.nat().try_scope(|elim| {
                            arbitrary_ty_under_ctx_with_depth(&elim.ctx(), depth, u)
                        })?;
                        let zero_inhab = arbitrary_term_of_ty_with_depth(
                            &motive.bind(&ctx.zero()),
                            depth,
                            u,
                        )?;
                        let succ_inhab = ctx.nat().try_scope(|elim| {
                            motive.bind(&elim).try_scope(|state| {
                                let motive = motive.weaken_into(&state.ctx());
                                arbitrary_term_of_ty_with_depth(
                                    &motive.bind(&elim.succs(1u32)),
                                    depth,
                                    u,
                                )
                            })
                        })?;
                        stuck.to_term().for_loop(
                            |elim| motive.bind(&elim),
                            &zero_inhab,
                            |elim, state| succ_inhab.bind(&elim).bind(&state),
                        )
                    },
                    (false, true) => {
                        let rhs = arbitrary_term_of_ty_with_depth(&ctx.nat(), depth, u)?;
                        Tm::max(&stuck.to_term(), &rhs)
                    },
                    (true, false) => {
                        let rhs = arbitrary_term_of_ty_with_depth(&ctx.nat(), depth, u)?;
                        stuck.to_term().add(&rhs)
                    },
                    (true, true) => {
                        let rhs = arbitrary_term_of_ty_with_depth(&ctx.nat(), depth, u)?;
                        stuck.to_term().mul(&rhs)
                    },
                }
            },

            TyKind::Equal { eq_term_0, eq_term_1 } => {
                let mut choices: Vec<Choice<'_, 'a, Tm<S>>> = Vec::new();
                choices.push(Box::new(|u| {
                    let motive = eq_term_0.ty().try_scope(|var_eq_term_0| {
                        var_eq_term_0.ty().try_scope(|var_eq_term_1| {
                            var_eq_term_0.equals(&var_eq_term_1).try_scope(|var_elim| {
                                arbitrary_ty_under_ctx_with_depth(&var_elim.ctx(), depth, u)
                            })
                        })
                    })?;
                    let inhab_ty = motive.map(|var_eq_term, inner| {
                        inner.bind(&var_eq_term).bind(&var_eq_term.refl())
                    });
                    let inhab = inhab_ty.try_map(|_var_eq_term, ty| {
                        arbitrary_term_of_ty_with_depth(&ty, depth, u)
                    })?;
                    Ok(stuck.to_term().cong(
                        |var_eq_term_0, var_eq_term_1, var_elim| {
                            motive.bind(&var_eq_term_0).bind(&var_eq_term_1).bind(&var_elim)
                        },
                        inhab.unbind(),
                    ))
                }));
                if eq_term_0 == eq_term_1 {
                    choices.push(Box::new(|u| {
                        let motive = eq_term_0.ty().try_scope(|var_eq_term| {
                            var_eq_term.equals(&var_eq_term).try_scope(|var_elim| {
                                arbitrary_ty_under_ctx_with_depth(&var_elim.ctx(), depth, u)
                            })
                        })?;
                        let inhab_ty = motive.map(|var_eq_term, inner| {
                            inner.bind(&var_eq_term.refl())
                        });
                        let inhab = inhab_ty.try_map(|_, inhab_ty| {
                            arbitrary_term_of_ty_with_depth(&inhab_ty, depth, u)
                        })?;
                        Ok(stuck.to_term().unique_identity(
                            |var_eq_term, var_elim| motive.bind(&var_eq_term).bind(&var_elim),
                            inhab.unbind(),
                        ))
                    }))
                }

                if let TmKind::Tag { tag: tag_0 } = eq_term_0.kind()
                && let TmKind::Tag { tag: tag_1 } = eq_term_1.kind()
                && tag_0 != tag_1
                {
                    choices.push(Box::new(|_| {
                        Ok(stuck.to_term().tags_apart())
                    }));
                }

                if let TmKind::Type { ty: ty_0 } = eq_term_0.kind()
                && let TmKind::Type { ty: ty_1 } = eq_term_1.kind()
                {
                    match (ty_0.kind(), ty_1.kind()) {
                        (TyKind::Equal { eq_term_0, .. }, TyKind::Equal { eq_term_1, .. }) => {
                            choices.push(Box::new(|_| {
                                Ok(stuck.to_term().equal_eq_eq_ty_injective())
                            }));
                            if eq_term_0.ty() == eq_term_1.ty() {
                                choices.push(Box::new(|_| {
                                    Ok(stuck.to_term().equal_eq_eq_term_0_injective())
                                }));
                                choices.push(Box::new(|_| {
                                    Ok(stuck.to_term().equal_eq_eq_term_1_injective())
                                }));
                            }
                        },
                        (TyKind::Sum { .. }, TyKind::Sum { .. }) => {
                            choices.push(Box::new(|_| {
                                Ok(stuck.to_term().sum_eq_lhs_injective())
                            }));
                            choices.push(Box::new(|_| {
                                Ok(stuck.to_term().sum_eq_rhs_injective())
                            }));
                        },
                        (
                            TyKind::Sigma { head_name: head_name_0, tail_ty: tail_ty_0 },
                            TyKind::Sigma { head_name: head_name_1, tail_ty: tail_ty_1 },
                        ) => {
                            choices.push(Box::new(|_| {
                                Ok(stuck.to_term().sigma_eq_head_injective())
                            }));
                            if head_name_0 == head_name_1
                            && tail_ty_0.var_ty() == tail_ty_1.var_ty() {
                                choices.push(Box::new(|_| {
                                    Ok(stuck.to_term().sigma_eq_tail_injective())
                                }));
                            }
                        },
                        (
                            TyKind::Pi { arg_name: arg_name_0, res_ty: res_ty_0 },
                            TyKind::Pi { arg_name: arg_name_1, res_ty: res_ty_1 },
                        ) => {
                            choices.push(Box::new(|_| {
                                Ok(stuck.to_term().pi_eq_arg_injective())
                            }));
                            if arg_name_0 == arg_name_1
                            && res_ty_0.var_ty() == res_ty_1.var_ty()
                            {
                                choices.push(Box::new(|_| {
                                    Ok(stuck.to_term().pi_eq_res_injective())
                                }));
                            }
                        },
                        _ => (),
                    }
                }
                let choice = u.choose_iter(choices.into_iter())?;
                choice(u)?
            },

            TyKind::Never => {
                let motive = stuck.ty().try_scope(|var_term| {
                    arbitrary_ty_under_ctx_with_depth(&var_term.ctx(), depth, u)
                })?;
                stuck.to_term().explode(motive.unbind())
            },

            TyKind::Unit => stuck.to_term(),

            TyKind::Sum { lhs_name: _, lhs_ty, rhs_ty } => {
                let lhs_inhab = lhs_ty.try_scope(|lhs_term| {
                    arbitrary_term_under_ctx_with_depth(&lhs_term.ctx(), depth, u)
                })?;
                let rhs_inhab = rhs_ty.try_scope(|rhs_term| {
                    arbitrary_term_under_ctx_with_depth(&rhs_term.ctx(), depth, u)
                })?;
                let motive = stuck.ty().scope(|elim| {
                    elim
                    .case(
                        |elim| elim.ctx().universe(),
                        |lhs_term| lhs_inhab.bind(&lhs_term).ty().to_term(),
                        |rhs_term| rhs_inhab.bind(&rhs_term).ty().to_term(),
                    )
                    .to_ty()
                });
                stuck.to_term().case(
                    motive.unbind(),
                    lhs_inhab.unbind(),
                    rhs_inhab.unbind(),
                )
            },

            TyKind::Sigma { head_name: _, tail_ty: _ } => {
                if u.arbitrary()? {
                    stuck.to_term().proj_head()
                } else {
                    stuck.to_term().proj_tail()
                }
            },

            TyKind::Pi { arg_name: _, res_ty } => {
                let arg_term = arbitrary_term_of_ty_with_depth(&res_ty.var_ty(), depth, u)?;
                stuck.to_term().app(&arg_term)
            },
        };
        match term.kind() {
            TmKind::Stuck { stuck } => Ok(stuck),
            _ => Ok(stuck),
        }
    } else {
        let mut indices = Vec::new();
        let stuck = loop {
            let mut index = u.choose_index(ctx.len() - indices.len())?;
            for prev_index in indices.iter().copied() {
                if index >= prev_index {
                    index += 1;
                }
            }
            if let TmKind::Stuck { stuck } = ctx.var(index).kind() {
                break stuck;
            }
            indices.push(index);
        };
        Ok(stuck)
    }
}

fn arbitrary_stuck_of_ty_with_depth<'a, S>(
    ty: &Ty<S>,
    depth: usize,
    u: &mut Unstructured<'a>,
) -> arbitrary::Result<Stuck<S>>
where
    S: Scheme,
    S::Tag: Arbitrary<'a>,
{
    // hack. prevent stack overflows until they're fixed.
    let depth = std::cmp::min(depth, MAX_DEPTH);

    if let Some(depth) = depth.checked_sub(2) && u.arbitrary()? {
        let stuck = arbitrary_stuck_under_ctx_with_depth(&ty.ctx(), depth, u)?;
        let term_opt = match stuck.ty().kind() {
            TyKind::Stuck { .. } |
            TyKind::Name |
            TyKind::Universe => None,

            TyKind::Nat => {
                if let TyKind::Nat = ty.kind() {
                    match (u.arbitrary()?, u.arbitrary()?) {
                        (false, false) => {
                            let zero_inhab = arbitrary_term_of_ty_with_depth(
                                &ty.ctx().nat(),
                                depth,
                                u,
                            )?;
                            let succ_inhab = ty.ctx().nat().try_scope(|elim| {
                                elim.ctx().nat().try_scope(|state| {
                                    arbitrary_term_of_ty_with_depth(
                                        &state.ctx().nat(),
                                        depth,
                                        u,
                                    )
                                })
                            })?;
                            Some(stuck.to_term().for_loop(
                                |elim| elim.ctx().nat(),
                                &zero_inhab,
                                |elim, state| succ_inhab.bind(&elim).bind(&state),
                            ))
                        },
                        (false, true) => {
                            let rhs = arbitrary_term_of_ty_with_depth(&ty.ctx().nat(), depth, u)?;
                            Some(Tm::max(&stuck.to_term(), &rhs))
                        },
                        (true, false) => {
                            let rhs = arbitrary_term_of_ty_with_depth(&ty.ctx().nat(), depth, u)?;
                            Some(stuck.to_term().add(&rhs))
                        },
                        (true, true) => {
                            let rhs = arbitrary_term_of_ty_with_depth(&ty.ctx().nat(), depth, u)?;
                            Some(stuck.to_term().mul(&rhs))
                        },
                    }
                } else {
                    let zero_inhab = arbitrary_term_of_ty_with_depth(
                        &ty,
                        depth,
                        u,
                    )?;
                    let succ_inhab = ty.ctx().nat().try_scope(|elim| {
                        ty.weaken_into(&elim.ctx()).try_scope(|state| {
                            arbitrary_term_of_ty_with_depth(
                                &ty.weaken_into(&state.ctx()),
                                depth,
                                u,
                            )
                        })
                    })?;
                    Some(stuck.to_term().for_loop(
                        |_| ty.clone(),
                        &zero_inhab,
                        |elim, state| succ_inhab.bind(&elim).bind(&state),
                    ))
                }
            },

            TyKind::Equal { eq_term_0, eq_term_1 } => {
                let mut choices: Vec<Choice<'_, 'a, Tm<S>>> = Vec::new();
                choices.push(Box::new(|u| {
                    let inhab = eq_term_0.ty().try_scope(|var_eq_term| {
                        let ty = ty.weaken_into(&var_eq_term.ctx());
                        arbitrary_term_of_ty_with_depth(&ty, depth, u)
                    })?;
                    Ok(stuck.to_term().cong(
                        |_, _, _| ty.clone(),
                        inhab.unbind(),
                    ))
                }));
                if eq_term_0 == eq_term_1 {
                    choices.push(Box::new(|u| {
                        let inhab = eq_term_0.ty().try_scope(|var_eq_term| {
                            let ty = ty.weaken_into(&var_eq_term.ctx());
                            arbitrary_term_of_ty_with_depth(&ty, depth, u)
                        })?;
                        Ok(stuck.to_term().unique_identity(
                            |_, _| ty.clone(),
                            inhab.unbind(),
                        ))
                    }))
                }

                if let TmKind::Tag { tag: tag_0 } = eq_term_0.kind()
                && let TmKind::Tag { tag: tag_1 } = eq_term_1.kind()
                && tag_0 != tag_1
                && let TyKind::Never = ty.kind()
                {
                    choices.push(Box::new(|_| {
                        Ok(stuck.to_term().tags_apart())
                    }));
                }

                if let TmKind::Type { ty: ty_0 } = eq_term_0.kind()
                && let TmKind::Type { ty: ty_1 } = eq_term_1.kind()
                {
                    match (ty_0.kind(), ty_1.kind()) {
                        (TyKind::Equal { eq_term_0, .. }, TyKind::Equal { eq_term_1, .. }) => {
                            let injectivity = stuck.to_term().equal_eq_eq_ty_injective();
                            if injectivity.ty() == *ty {
                                choices.push(Box::new(move |_| {
                                    Ok(injectivity.clone())
                                }));
                            }

                            if eq_term_0.ty() == eq_term_1.ty() {
                                let injectivity = stuck.to_term().equal_eq_eq_term_0_injective();
                                if injectivity.ty() == *ty {
                                    choices.push(Box::new(move |_| {
                                        Ok(injectivity.clone())
                                    }));
                                }
                                let injectivity = stuck.to_term().equal_eq_eq_term_1_injective();
                                if injectivity.ty() == *ty {
                                    choices.push(Box::new(move |_| {
                                        Ok(injectivity.clone())
                                    }));
                                }
                            }
                        },
                        (TyKind::Sum { .. }, TyKind::Sum { .. }) => {
                            let injectivity = stuck.to_term().sum_eq_name_injective();
                            if injectivity.ty() == *ty {
                                choices.push(Box::new(move |_| {
                                    Ok(injectivity.clone())
                                }));
                            }
                            let injectivity = stuck.to_term().sum_eq_lhs_injective();
                            if injectivity.ty() == *ty {
                                choices.push(Box::new(move |_| {
                                    Ok(injectivity.clone())
                                }));
                            }
                            let injectivity = stuck.to_term().sum_eq_rhs_injective();
                            if injectivity.ty() == *ty {
                                choices.push(Box::new(move |_| {
                                    Ok(injectivity.clone())
                                }));
                            }
                        },
                        (
                            TyKind::Sigma { head_name: head_name_0, tail_ty: tail_ty_0 },
                            TyKind::Sigma { head_name: head_name_1, tail_ty: tail_ty_1 },
                        ) => {
                            let injectivity = stuck.to_term().sigma_eq_name_injective();
                            if injectivity.ty() == *ty {
                                choices.push(Box::new(move |_| {
                                    Ok(injectivity.clone())
                                }));
                            }
                            let injectivity = stuck.to_term().sigma_eq_head_injective();
                            if injectivity.ty() == *ty {
                                choices.push(Box::new(move |_| {
                                    Ok(injectivity.clone())
                                }));
                            }

                            if head_name_0 == head_name_1
                            && tail_ty_0.var_ty() == tail_ty_1.var_ty()
                            {
                                let injectivity = stuck.to_term().sigma_eq_tail_injective();
                                if injectivity.ty() == *ty {
                                    choices.push(Box::new(move |_| {
                                        Ok(injectivity.clone())
                                    }));
                                }
                            }
                        },
                        (
                            TyKind::Pi { arg_name: arg_name_0, res_ty: res_ty_0 },
                            TyKind::Pi { arg_name: arg_name_1, res_ty: res_ty_1 },
                        ) => {
                            let injectivity = stuck.to_term().pi_eq_name_injective();
                            if injectivity.ty() == *ty {
                                choices.push(Box::new(move |_| {
                                    Ok(injectivity.clone())
                                }));
                            }
                            let injectivity = stuck.to_term().pi_eq_arg_injective();
                            if injectivity.ty() == *ty {
                                choices.push(Box::new(move |_| {
                                    Ok(injectivity.clone())
                                }));
                            }

                            if arg_name_0 == arg_name_1
                            && res_ty_0.var_ty() == res_ty_1.var_ty()
                            {
                                let injectivity = stuck.to_term().pi_eq_res_injective();
                                if injectivity.ty() == *ty {
                                    choices.push(Box::new(move |_| {
                                        Ok(injectivity.clone())
                                    }));
                                }
                            }
                        },
                        _ => (),
                    }
                }
                let choice = u.choose_iter(choices.into_iter())?;
                Some(choice(u)?)
            },

            TyKind::Never => {
                Some(stuck.to_term().explode(|_| ty.clone()))
            },

            TyKind::Unit => None,

            TyKind::Sum { lhs_name: _, lhs_ty, rhs_ty } => {
                let lhs_inhab = lhs_ty.try_scope(|lhs_term| {
                    arbitrary_term_of_ty_with_depth(&ty.weaken_into(&lhs_term.ctx()), depth, u)
                })?;
                let rhs_inhab = rhs_ty.try_scope(|rhs_term| {
                    arbitrary_term_of_ty_with_depth(&ty.weaken_into(&rhs_term.ctx()), depth, u)
                })?;
                Some(stuck.to_term().case(
                    |_| ty.clone(),
                    lhs_inhab.unbind(),
                    rhs_inhab.unbind(),
                ))
            },

            TyKind::Sigma { head_name: _, tail_ty } => {
                let mut choices: Vec<Choice<'_, 'a, Tm<S>>> = Vec::new();
                if tail_ty.var_ty() == *ty {
                    choices.push(Box::new(|_| {
                        Ok(stuck.to_term().proj_head())
                    }));
                }
                if tail_ty.bind(&stuck.to_term().proj_head()) == *ty {
                    choices.push(Box::new(|_| {
                        Ok(stuck.to_term().proj_tail())
                    }));
                }
                let choice = u.choose_iter(choices.into_iter())?;
                Some(choice(u)?)
            },

            TyKind::Pi { arg_name: _, res_ty } => {
                let arg_ty = res_ty.var_ty();
                if let Some(res_ty) = res_ty.try_strengthen() && res_ty == *ty {
                    let arg_term = arbitrary_term_of_ty_with_depth(&arg_ty, depth, u)?;
                    Some(stuck.to_term().app(&arg_term))
                } else {
                    None
                }
            },
        };
        match term_opt {
            Some(term) => match term.kind() {
                TmKind::Stuck { stuck } => Ok(stuck),
                _ => Ok(stuck),
            }
            None => Ok(stuck),
        }
    } else {
        let mut indices = Vec::new();
        let stuck = loop {
            let mut index = u.choose_index(ty.ctx().len() - indices.len())?;
            for prev_index in indices.iter().copied() {
                if index >= prev_index {
                    index += 1;
                }
            }
            if let TmKind::Stuck { stuck } = ty.ctx().var(index).kind() {
                break stuck;
            }
            indices.push(index);
        };
        Ok(stuck)
    }
}

fn arbitrary_name_under_ctx_with_depth<'a, S>(
    ctx: &Ctx<S>,
    depth: usize,
    u: &mut Unstructured<'a>,
) -> arbitrary::Result<Name<S>>
where
    S: Scheme,
    S::Tag: Arbitrary<'a>,
{
    if let Some(depth) = depth.checked_sub(1) {
        let num_name_vars = {
            let mut ctx = ctx.clone();
            let mut num_name_vars = 0;
            while let Some(var_ty) = ctx.pop() {
                if let TyKind::Name = var_ty.kind() {
                    num_name_vars += 1;
                }
                ctx = var_ty.ctx();
            }
            num_name_vars
        };
        if u.choose_index(num_name_vars + 1)? > 0 {
            let stuck = arbitrary_stuck_of_ty_with_depth(&ctx.name(), depth, u)?;
            return Ok(stuck.to_name());
        }
    }
    let tag = u.arbitrary()?;
    Ok(ctx.tag(&tag))
}



/*
#[test]
fn check_ctx_depths() {
    let mut buffer = [0u8; 1 << 20];
    let mut points = Vec::new();
    for depth in 0..50 {
        //for _ in 0..100 {
        let mut max_used = 0;
        for _ in 0..1000 {
            rand::fill(&mut buffer);
            let mut u = Unstructured::new(&buffer);
            let _ctx = arbitrary_ctx_with_depth(depth, &mut u);
            let remaining = u.len();
            assert!(remaining > buffer.len() / 2);
            let used = buffer.len().strict_sub(remaining);
            max_used = cmp::max(max_used, used);
        }
        points.push((depth, max_used));
    }
    for (depth, used) in points {
        println!("{}, {}", depth, used);
    }
}

#[test]
fn check_ty_depths() {
    let mut buffer = [0u8; 1 << 20];
    let mut points = Vec::new();
    for depth in 0..50usize {
        //for _ in 0..100 {
        let mut max_used = 0;
        for _ in 0..1000 {
            rand::fill(&mut buffer);
            let mut u = Unstructured::new(&buffer);
            let Ok(ctx) = arbitrary_ctx_with_depth(depth.saturating_sub(2), &mut u) else {
                continue;
            };
            let _ty = arbitrary_ty_under_ctx_with_depth(&ctx, depth.saturating_sub(2), &mut u);
            let remaining = u.len();
            assert!(remaining > buffer.len() / 2);
            let used = buffer.len().strict_sub(remaining);
            max_used = cmp::max(max_used, used);
        }
        points.push((depth, max_used));
    }
    for (depth, used) in points {
        println!("{}, {}", depth, used);
    }
}

#[test]
fn check_term_depths() {
    let mut buffer = [0u8; 1 << 20];
    let mut points = Vec::new();
    for depth in 0..50usize {
        //for _ in 0..100 {
        let mut max_used = 0;
        for _ in 0..1000 {
            rand::fill(&mut buffer);
            let mut u = Unstructured::new(&buffer);
            let Ok(ctx) = arbitrary_ctx_with_depth(depth.saturating_sub(2), &mut u) else {
                continue;
            };
            let _term = arbitrary_term_under_ctx_with_depth(&ctx, depth.saturating_sub(2), &mut u);
            let remaining = u.len();
            assert!(remaining > buffer.len() / 2);
            let used = buffer.len().strict_sub(remaining);
            max_used = cmp::max(max_used, used);
        }
        points.push((depth, max_used));
    }
    for (depth, used) in points {
        println!("{}, {}", depth, used);
    }
}

#[test]
fn check_stuck_depths() {
    let mut buffer = [0u8; 1 << 20];
    let mut points = Vec::new();
    for depth in 0..50usize {
        //for _ in 0..100 {
        let mut max_used = 0;
        for _ in 0..1000 {
            rand::fill(&mut buffer);
            let mut u = Unstructured::new(&buffer);
            let Ok(ctx) = arbitrary_ctx_with_depth(depth.saturating_sub(2), &mut u) else {
                continue;
            };
            let _stuck = arbitrary_stuck_under_ctx_with_depth(&ctx, depth.saturating_sub(2), &mut u);
            let remaining = u.len();
            assert!(remaining > buffer.len() / 2);
            let used = buffer.len().strict_sub(remaining);
            max_used = cmp::max(max_used, used);
        }
        points.push((depth, max_used));
    }
    for (depth, used) in points {
        println!("{}, {}", depth, used);
    }
}

#[test]
fn check_term_of_ty_depths() {
    let mut buffer = [0u8; 1 << 20];
    let mut points = Vec::new();
    for depth in 0..50usize {
        //for _ in 0..100 {
        let mut max_used = 0;
        for _ in 0..1000 {
            rand::fill(&mut buffer);
            let mut u = Unstructured::new(&buffer);
            let Ok(ctx) = arbitrary_ctx_with_depth(depth, &mut u) else {
                continue;
            };
            let Ok(ty) = arbitrary_ty_under_ctx_with_depth(&ctx, depth, &mut u) else {
                continue;
            };
            let remaining_before = u.len();
            let _term = arbitrary_term_of_ty_with_depth(&ty, depth, &mut u);
            let remaining = u.len();
            assert!(remaining > buffer.len() / 2);
            let used = remaining_before.strict_sub(remaining);
            max_used = cmp::max(max_used, used);
        }
        points.push((depth, max_used));
    }
    for (depth, used) in points {
        println!("{}, {}", depth, used);
    }
}
*/

