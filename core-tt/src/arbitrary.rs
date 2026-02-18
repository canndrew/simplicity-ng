use crate::priv_prelude::*;

// FIXME: hack to prevent stack overflows until they're fixed.
const MAX_DEPTH: usize = 10;

impl<'a, S> Arbitrary<'a> for Ctx<S>
where
    S: Scheme,
    S::UserTy: Arbitrary<'a>,
    S::UserTm: Arbitrary<'a>,
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
    S::UserTy: Arbitrary<'a>,
    S::UserTm: Arbitrary<'a>,
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
    S::UserTy: Arbitrary<'a>,
    S::UserTm: Arbitrary<'a>,
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
    S::UserTy: Arbitrary<'a>,
    S::UserTm: Arbitrary<'a>,
{
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Stuck<S>> {
        let depth = u.len() / 8;
        let ctx = arbitrary_ctx_with_depth(depth.saturating_sub(2), u)?;
        arbitrary_stuck_under_ctx_with_depth(&ctx, depth.saturating_sub(2), u)
    }
}

pub fn arbitrary_ctx<'a, S>(
    u: &mut Unstructured<'a>,
) -> arbitrary::Result<Ctx<S>>
where
    S: Scheme,
    S::UserTy: Arbitrary<'a>,
    S::UserTm: Arbitrary<'a>,
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
    S::UserTy: Arbitrary<'a>,
    S::UserTm: Arbitrary<'a>,
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
    S::UserTy: Arbitrary<'a>,
    S::UserTm: Arbitrary<'a>,
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
    S::UserTy: Arbitrary<'a>,
    S::UserTm: Arbitrary<'a>,
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
    S::UserTy: Arbitrary<'a>,
    S::UserTm: Arbitrary<'a>,
{
    let depth = u.len() / 4;
    arbitrary_stuck_under_ctx_with_depth(&ctx, depth, u)
}

fn arbitrary_ctx_with_depth<'a, S>(
    depth: usize,
    u: &mut Unstructured<'a>,
) -> arbitrary::Result<Ctx<S>>
where
    S: Scheme,
    S::UserTy: Arbitrary<'a>,
    S::UserTm: Arbitrary<'a>,
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
    S::UserTy: Arbitrary<'a>,
    S::UserTm: Arbitrary<'a>,
{
    // hack. prevent stack overflows until they're fixed.
    let depth = std::cmp::min(depth, MAX_DEPTH);

    let mut choices: Vec<Box<dyn Fn(&mut Unstructured<'a>) -> arbitrary::Result<Ty<S>>>>  = Vec::new();
    choices.push(Box::new(move |_u| Ok(ctx.universe())));
    choices.push(Box::new(move |_u| Ok(ctx.nat())));
    choices.push(Box::new(move |_u| Ok(ctx.never())));
    choices.push(Box::new(move |_u| Ok(ctx.unit_ty())));
    choices.push(Box::new(move |u| {
        let user_ty = u.arbitrary()?;
        Ok(ctx.user_ty(&user_ty))
    }));
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
            let lhs_ty = arbitrary_ty_under_ctx_with_depth(ctx, depth, u)?;
            let rhs_ty = arbitrary_ty_under_ctx_with_depth(ctx, depth, u)?;
            Ok(Ty::sum(&lhs_ty, &rhs_ty))
        }));
        choices.push(Box::new(move |u| {
            let head_ty = arbitrary_ty_under_ctx_with_depth(ctx, depth, u)?;
            let tail_ty = head_ty.try_scope(|head_term| {
                arbitrary_ty_under_ctx_with_depth(&head_term.ctx(), depth, u)
            })?;
            Ok(head_ty.sigma(tail_ty.unbind()))
        }));
        choices.push(Box::new(move |u| {
            let arg_ty = arbitrary_ty_under_ctx_with_depth(ctx, depth, u)?;
            let res_ty = arg_ty.try_scope(|arg_term| {
                arbitrary_ty_under_ctx_with_depth(&arg_term.ctx(), depth, u)
            })?;
            Ok(arg_ty.pi(res_ty.unbind()))
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
    S::UserTy: Arbitrary<'a>,
    S::UserTm: Arbitrary<'a>,
{
    // hack. prevent stack overflows until they're fixed.
    let depth = std::cmp::min(depth, MAX_DEPTH);

    let mut choices: Vec<Box<dyn Fn(&mut Unstructured<'a>) -> arbitrary::Result<Tm<S>>>>  = Vec::new();
    choices.push(Box::new(move |_u| Ok(ctx.unit_term())));
    choices.push(Box::new(move |u| {
        let user_term = u.arbitrary()?;
        Ok(ctx.user_term(&user_term))
    }));
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
            let lhs_term = arbitrary_term_under_ctx_with_depth(ctx, depth, u)?;
            let rhs_ty = arbitrary_ty_under_ctx_with_depth(ctx, depth, u)?;
            Ok(lhs_term.inj_lhs(&rhs_ty))
        }));
        choices.push(Box::new(move |u| {
            let rhs_term = arbitrary_term_under_ctx_with_depth(ctx, depth, u)?;
            let lhs_ty = arbitrary_ty_under_ctx_with_depth(ctx, depth, u)?;
            Ok(rhs_term.inj_rhs(&lhs_ty))
        }));
        choices.push(Box::new(move |u| {
            let head_term = arbitrary_term_under_ctx_with_depth(ctx, depth, u)?;
            let tail_term = head_term.ty().try_scope(|head_term| {
                arbitrary_term_under_ctx_with_depth(&head_term.ctx(), depth, u)
            })?;
            let tail_ty = tail_term.map(|_head_term, term| term.ty());
            let tail_term = tail_term.bind(&head_term);
            Ok(head_term.pair(tail_ty.unbind(), &tail_term))
        }));
        choices.push(Box::new(move |u| {
            let arg_ty = arbitrary_ty_under_ctx_with_depth(ctx, depth, u)?;
            let res_term = arg_ty.try_scope(|arg_term| {
                arbitrary_term_under_ctx_with_depth(&arg_term.ctx(), depth, u)
            })?;
            Ok(arg_ty.func(res_term.unbind()))
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
    S::UserTy: Arbitrary<'a>,
    S::UserTm: Arbitrary<'a>,
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
                TyKind::User { .. } => None,
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
                TyKind::Sum { lhs_ty, rhs_ty } => {
                    if let Some(depth) = depth.checked_sub(1) {
                        if u.arbitrary()? {
                            Some(
                                arbitrary_term_of_ty_with_depth(&lhs_ty, depth, u)?
                                .inj_lhs(&rhs_ty)
                            )
                        } else {
                            Some(
                                arbitrary_term_of_ty_with_depth(&rhs_ty, depth, u)?
                                .inj_rhs(&lhs_ty)
                            )
                        }
                    } else {
                        None
                    }
                },
                TyKind::Sigma { tail_ty } => {
                    if let Some(depth) = depth.checked_sub(1) {
                        let head_term = arbitrary_term_of_ty_with_depth(&tail_ty.var_ty(), depth, u)?;
                        let substituted_tail_ty = tail_ty.bind(&head_term);
                        let tail_term = arbitrary_term_of_ty_with_depth(&substituted_tail_ty, depth, u)?;
                        let term = head_term.pair(
                            tail_ty.unbind(),
                            &tail_term,
                        );
                        Some(term)
                    } else {
                        None
                    }
                },
                TyKind::Pi { res_ty } => {
                    if let Some(depth) = depth.checked_sub(1) {
                        let res_term = res_ty.var_ty().try_scope(|arg_term| {
                            arbitrary_term_of_ty_with_depth(&res_ty.bind(&arg_term), depth, u)
                        })?;
                        Some(res_ty.var_ty().func(res_term.unbind()))
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
    S::UserTy: Arbitrary<'a>,
    S::UserTm: Arbitrary<'a>,
{
    // hack. prevent stack overflows until they're fixed.
    let depth = std::cmp::min(depth, MAX_DEPTH);

    if let Some(depth) = depth.checked_sub(2) && u.arbitrary()? {
        let stuck = arbitrary_stuck_under_ctx_with_depth(ctx, depth, u)?;
        let term = match stuck.ty().kind() {
            TyKind::Stuck { .. } |
            TyKind::User { .. } |
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
                        stuck.to_term().max(&rhs)
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

            TyKind::Equal { eq_term_0, .. } => {
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
                stuck.to_term().cong(
                    |var_eq_term_0, var_eq_term_1, var_elim| {
                        motive.bind(&var_eq_term_0).bind(&var_eq_term_1).bind(&var_elim)
                    },
                    inhab.unbind(),
                )
            },

            TyKind::Never => {
                let motive = stuck.ty().try_scope(|var_term| {
                    arbitrary_ty_under_ctx_with_depth(&var_term.ctx(), depth, u)
                })?;
                stuck.to_term().explode(motive.unbind())
            },

            TyKind::Unit => stuck.to_term(),

            TyKind::Sum { lhs_ty, rhs_ty } => {
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

            TyKind::Sigma { tail_ty: _ } => {
                if u.arbitrary()? {
                    stuck.to_term().proj_head()
                } else {
                    stuck.to_term().proj_tail()
                }
            },

            TyKind::Pi { res_ty } => {
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

