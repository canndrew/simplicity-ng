use crate::priv_prelude::*;

thread_local! {
    pub static INDENT: Cell<usize> = const { Cell::new(0) };
}

fn newline(f: &mut fmt::Formatter) -> fmt::Result {
    writeln!(f, "")?;
    for _ in 0..INDENT.get() {
        write!(f, "    ")?;
    }
    Ok(())
}

fn indent(f: &mut fmt::Formatter, func: impl FnOnce(&mut fmt::Formatter) -> fmt::Result) -> fmt::Result {
    const MAX_INDENT: usize = 30;

    let i = INDENT.get();
    if i < MAX_INDENT {
        INDENT.set(i + 1);
        let ret = func(f);
        INDENT.set(i);
        ret
    } else {
        write!(f, "...")
    }
}

macro_rules! args (
    ($f:ident, $name:literal, []) => ({
        write!($f, "{}()", $name)?;
    });
    ($f:ident, $name:literal, [$($($field_name:ident = $x:expr),+ $(,)?)?]) => ({
        write!($f, "{}(", $name)?;
        indent($f, |$f| {
            $($(
                newline($f)?;
                write!($f, "{} = ", stringify!($field_name))?;
                $x?;
                write!($f, ",")?;
            )+)?
            Ok(())
        })?;
        newline($f)?;
        write!($f, ")")?;
    });
);

impl<S: Scheme> fmt::Debug for Ctx<S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        pprint_raw_ctx(&self.raw_ctx, f)?;
        Ok(())
    }
}

impl<S: Scheme> fmt::Debug for Ty<S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Ty {{")?;
        indent(f, |f| {
            newline(f)?;
            if f.alternate() {
                write!(f, "ctx: ")?;
                pprint_raw_ctx(&self.raw_ctx, f)?;
                write!(f, ",")?;
                newline(f)?;
            }
            write!(f, "raw_ty: ")?;
            pprint_raw_ty(&self.raw_ctx, Usages::ones(self.raw_ty.usages.len()), &self.raw_ty, f)?;
            write!(f, ",")?;
            Ok(())
        })?;
        newline(f)?;
        write!(f, "}}")?;
        Ok(())
    }
}

impl<S: Scheme> fmt::Debug for Tm<S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (raw_ty, raw_term) = self.raw_typed_term.to_parts();
        write!(f, "Tm {{")?;
        indent(f, |f| {
            newline(f)?;
            if f.alternate() {
                write!(f, "ctx: ")?;
                pprint_raw_ctx(&self.raw_ctx, f)?;
                write!(f, ",")?;
                newline(f)?;
                write!(f, "raw_ty: ")?;
                pprint_raw_ty(&self.raw_ctx, Usages::ones(raw_ty.usages.len()), &raw_ty, f)?;
                write!(f, ",")?;
                newline(f)?;
            }
            write!(f, "raw_term: ")?;
            pprint_raw_term(
                &self.raw_ctx,
                Usages::ones(raw_ty.usages.len()),
                &raw_ty,
                Usages::ones(raw_term.usages.len()),
                &raw_term,
                f,
            )?;
            write!(f, ",")?;
            Ok(())
        })?;
        newline(f)?;
        write!(f, "}}")?;
        Ok(())
    }
}

impl<S: Scheme> fmt::Debug for Stuck<S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (raw_ty, raw_stuck) = self.raw_typed_stuck.to_parts();
        write!(f, "Stuck {{")?;
        indent(f, |f| {
            newline(f)?;
            if f.alternate() {
                write!(f, "ctx: ")?;
                pprint_raw_ctx(&self.raw_ctx, f)?;
                write!(f, ",")?;
                newline(f)?;
                write!(f, "raw_ty: ")?;
                pprint_raw_ty(&self.raw_ctx, Usages::ones(raw_ty.usages.len()), &raw_ty, f)?;
                write!(f, ",")?;
                newline(f)?;
            }
            write!(f, "raw_stuck: ")?;
            pprint_raw_stuck(
                &self.raw_ctx,
                Usages::ones(raw_stuck.usages.len()),
                &raw_stuck,
                f,
            )?;
            write!(f, ",")?;
            Ok(())
        })?;
        newline(f)?;
        write!(f, "}}")?;
        Ok(())
    }
}

impl<S: Scheme, T: Contextual<S> + fmt::Debug> fmt::Debug for Scope<S, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Scope {{")?;
        indent(f, |f| {
            newline(f)?;
            if f.alternate() {
                write!(f, "ctx: ")?;
                pprint_raw_ctx(&self.raw_ctx, f)?;
                write!(f, ",")?;
                newline(f)?;
            }
            write!(f, "raw_scope: ")?;
            pprint_raw_scope(
                &self.raw_ctx,
                Usages::ones(self.raw_scope.usages.len()),
                &self.raw_scope,
                |raw_ctx, filter, inner, f| {
                    let ctx = Ctx { raw_ctx: raw_ctx.clone() };
                    let inner = inner.clone_unfilter(&filter);
                    let inner = T::from_raw(ctx, inner);
                    fmt::Debug::fmt(&inner, f)
                },
                f,
            )?;
            write!(f, ",")?;
            Ok(())
        })?;
        newline(f)?;
        write!(f, "}}")?;
        Ok(())
    }
}

fn pprint_raw_ctx_inner<S: Scheme>(raw_ctx: &RawCtx<S>, f: &mut fmt::Formatter) -> Result<usize, fmt::Error> {
    match &raw_ctx.cons_opt {
        None => Ok(0),
        Some(cons) => {
            let RawCtxCons { parent, var_ty } = &**cons;
            let ctx_len = pprint_raw_ctx_inner(parent, f)?;
            newline(f)?;
            write!(f, "{}: ", ctx_len)?;
            let filter = Usages::ones(ctx_len);
            pprint_raw_ty(parent, filter, var_ty, f)?;
            Ok(ctx_len + 1)
        },
    }
}

pub fn pprint_raw_ctx<S: Scheme>(raw_ctx: &RawCtx<S>, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "[")?;
    indent(f, |f| {
        let _ctx_len = pprint_raw_ctx_inner(raw_ctx, f)?;
        Ok(())
    })?;
    newline(f)?;
    write!(f, "]")?;
    Ok(())
}

pub fn pprint_raw_ty<S: Scheme>(
    raw_ctx: &RawCtx<S>,
    mut filter: Usages,
    raw_ty: &RawTy<S>,
    f: &mut fmt::Formatter,
) -> fmt::Result {
    filter.zero_unused(&raw_ty.usages);
    pprint_raw_ty_kind(raw_ctx, filter, raw_ty.weak, f)
}

fn pprint_raw_term<S: Scheme>(
    raw_ctx: &RawCtx<S>,
    mut ty_filter: Usages,
    raw_ty: &RawTy<S>,
    mut term_filter: Usages,
    raw_term: &RawTm<S>,
    f: &mut fmt::Formatter,
) -> fmt::Result {
    ty_filter.zero_unused(&raw_ty.usages);
    term_filter.zero_unused(&raw_term.usages);
    pprint_raw_term_kind(raw_ctx, ty_filter, raw_ty.weak, term_filter, raw_term.weak, f)
}

fn pprint_raw_stuck<S: Scheme>(
    raw_ctx: &RawCtx<S>,
    mut filter: Usages,
    raw_stuck: &RawStuck<S>,
    f: &mut fmt::Formatter,
) -> fmt::Result {
    filter.zero_unused(&raw_stuck.usages);
    pprint_raw_stuck_kind(raw_ctx, filter, raw_stuck.weak, f)
}

fn pprint_raw_ty_kind<S: Scheme>(
    raw_ctx: &RawCtx<S>,
    filter: Usages,
    raw_ty_kind: Intern<RawTyKind<S>>,
    f: &mut fmt::Formatter,
) -> fmt::Result {
    match raw_ty_kind.get_clone() {
        RawTyKind::Stuck { stuck } => {
            args!(f, "stuck", [
                stuck = pprint_raw_stuck(raw_ctx, filter, &stuck, f),
            ])
        },
        RawTyKind::User { user_ty } => {
            args!(f, "user", [
                user_ty = write!(f, "{:?}", user_ty),
            ])
        },
        RawTyKind::Universe => {
            args!(f, "universe", []);
        },
        RawTyKind::Nat => {
            args!(f, "nat", []);
        },
        RawTyKind::Equal { eq_ty, eq_term_0, eq_term_1 } => {
            args!(f, "equal", [
                eq_ty = pprint_raw_ty(raw_ctx, filter.clone(), &eq_ty, f),
                eq_term_0 = pprint_raw_term(raw_ctx, filter.clone(), &eq_ty, filter.clone(), &eq_term_0, f),
                eq_term_1 = pprint_raw_term(raw_ctx, filter.clone(), &eq_ty, filter.clone(), &eq_term_1, f),
            ]);
        },
        RawTyKind::Never => {
            args!(f, "never", []);
        },
        RawTyKind::Unit => {
            args!(f, "unit", []);
        },
        RawTyKind::Sum { lhs_ty, rhs_ty } => {
            args!(f, "sum", [
                lhs_ty = pprint_raw_ty(raw_ctx, filter.clone(), &lhs_ty, f),
                rhs_ty = pprint_raw_ty(raw_ctx, filter, &rhs_ty, f),
            ]);
        },
        RawTyKind::Sigma { tail_ty } => {
            args!(f, "sigma", [
                tail_ty = pprint_raw_scope(
                    raw_ctx,
                    filter.clone(),
                    &tail_ty,
                    |raw_ctx, filter, tail_ty, f| {
                        pprint_raw_ty(raw_ctx, filter, tail_ty, f)
                    },
                    f,
                ),
            ]);
        },
        RawTyKind::Pi { res_ty } => {
            args!(f, "pi", [
                res_ty = pprint_raw_scope(
                    raw_ctx,
                    filter.clone(),
                    &res_ty,
                    |raw_ctx, filter, res_ty, f| {
                        pprint_raw_ty(raw_ctx, filter, res_ty, f)
                    },
                    f,
                ),
            ]);
        },
    }
    Ok(())
}

fn pprint_raw_term_kind<S: Scheme>(
    raw_ctx: &RawCtx<S>,
    mut ty_filter: Usages,
    raw_ty_kind: Intern<RawTyKind<S>>,
    term_filter: Usages,
    raw_term_kind: Intern<RawTmKind<S>>,
    f: &mut fmt::Formatter,
) -> fmt::Result {
    match raw_term_kind.get_clone() {
        RawTmKind::Stuck { stuck } => {
            args!(f, "stuck", [
                stuck = pprint_raw_stuck(raw_ctx, term_filter, &stuck, f),
            ]);
        },
        RawTmKind::User { user_term } => {
            debug_assert!(ty_filter.is_zeros());
            args!(f, "user", [
                user_term = write!(f, "{:?}", user_term),
            ]);
        },
        RawTmKind::Type { ty } => {
            debug_assert!(ty_filter.is_zeros());
            debug_assert!(matches!(raw_ty_kind.get_clone(), RawTyKind::Universe));
            args!(f, "type", [
                ty = pprint_raw_ty(raw_ctx, term_filter, &ty, f),
            ]);
        },
        RawTmKind::Zero => {
            debug_assert!(ty_filter.is_zeros());
            debug_assert!(matches!(raw_ty_kind.get_clone(), RawTyKind::Nat));
            args!(f, "zero", []);
        },
        RawTmKind::Succs { count, pred_term } => {
            debug_assert!(ty_filter.is_zeros());
            debug_assert!(matches!(raw_ty_kind.get_clone(), RawTyKind::Nat));
            args!(f, "succs", [
                count = write!(f, "{}", count),
                pred_term = pprint_raw_term(raw_ctx, ty_filter, &RawTy::nat(0), term_filter, &pred_term, f),
            ]);
        },
        RawTmKind::Refl => {
            let RawTyKind::Equal { eq_ty, eq_term_0, eq_term_1 } = raw_ty_kind.get_clone() else {
                unreachable!();
            };
            debug_assert_eq!(eq_term_0, eq_term_1);
            args!(f, "refl", [
                eq_term = pprint_raw_term(raw_ctx, ty_filter.clone(), &eq_ty, ty_filter, &eq_term_0, f),
            ])
        },
        RawTmKind::Unit => {
            args!(f, "unit", []);
        },
        RawTmKind::InjLhs { lhs_term } => {
            let RawTyKind::Sum { lhs_ty, rhs_ty: _ } = raw_ty_kind.get_clone() else {
                unreachable!();
            };
            args!(f, "inj_lhs", [
                lhs_term = pprint_raw_term(raw_ctx, ty_filter, &lhs_ty, term_filter, &lhs_term, f),
            ]);
        },
        RawTmKind::InjRhs { rhs_term } => {
            let RawTyKind::Sum { lhs_ty: _, rhs_ty } = raw_ty_kind.get_clone() else {
                unreachable!();
            };
            args!(f, "inj_rhs", [
                rhs_term = pprint_raw_term(raw_ctx, ty_filter, &rhs_ty, term_filter, &rhs_term, f),
            ]);
        },
        RawTmKind::Pair { head_term, tail_term } => {
            let RawTyKind::Sigma { tail_ty } = raw_ty_kind.get_clone() else {
                unreachable!();
            };
            let head_ty = &tail_ty.weak.var_ty;
            let head_ty_filter = {
                let mut head_ty_filter = ty_filter.clone();
                head_ty_filter.zero_unused(&tail_ty.usages);
                head_ty_filter
            };
            let tail_ty = {
                tail_ty
                .clone_unfilter(&ty_filter)
                .bind(&head_term.clone_unfilter(&term_filter))
            };
            let (tail_ty_filter, tail_ty) = tail_ty.filter_self();
            args!(f, "pair", [
                head_term = pprint_raw_term(raw_ctx, head_ty_filter, head_ty, term_filter.clone(), &head_term, f),
                tail_term = pprint_raw_term(raw_ctx, tail_ty_filter, &tail_ty, term_filter, &tail_term, f),
            ]);
        },
        RawTmKind::Func { res_term } => {
            let RawTyKind::Pi { res_ty } = raw_ty_kind.get_clone() else {
                unreachable!();
            };
            args!(f, "func", [
                res_term = pprint_raw_scope(
                    raw_ctx,
                    term_filter,
                    &res_term,
                    |ctx, term_filter, res_term, f| {
                        ty_filter.zero_unused(&res_ty.usages);
                        ty_filter.push(true);
                        pprint_raw_term(ctx, ty_filter, &res_ty.weak.inner, term_filter, res_term, f)
                    },
                    f,
                ),
            ]);
        },
    }
    Ok(())
}

fn pprint_raw_stuck_kind<S: Scheme>(
    raw_ctx: &RawCtx<S>,
    filter: Usages,
    raw_stuck_kind: Intern<RawStuckKind<S>>,
    f: &mut fmt::Formatter,
) -> fmt::Result {
    match raw_stuck_kind.get_clone() {
        RawStuckKind::Var => {
            let index = filter.index_of_single_one().unwrap();
            write!(f, "var({})", index)?;
        },

        RawStuckKind::ForLoop { elim, motive, zero_inhab, succ_inhab } => {
            args!(f, "for_loop", [
                elim = pprint_raw_stuck(raw_ctx, filter.clone(), &elim, f),
                moitve = pprint_raw_scope(
                    raw_ctx,
                    filter.clone(),
                    &motive,
                    |raw_ctx, inner_filter, motive, f| {
                        pprint_raw_ty(raw_ctx, inner_filter, motive, f)
                    },
                    f,
                ),
                zero_inhab = pprint_raw_term(
                    raw_ctx,
                    filter.clone(),
                    &motive.clone().bind(&RawTm::zero(motive.usages.len())),
                    filter.clone(),
                    &zero_inhab,
                    f,
                ),
                succ_inhab = pprint_raw_scope(
                    raw_ctx,
                    filter.clone(),
                    &succ_inhab,
                    |raw_ctx, inner_filter, succ_inhab, f| {
                        pprint_raw_scope(
                            raw_ctx,
                            inner_filter,
                            succ_inhab,
                            |raw_ctx, inner_filter, succ_inhab, f| {
                                let succ_inhab_ty = {
                                    let mut succ_inhab_ty = motive.clone();
                                    succ_inhab_ty.weaken(2);
                                    succ_inhab_ty.bind(
                                        &RawTm::succs(
                                            NonZeroBigUint::one(),
                                            RawTm::var(
                                                motive.usages.len() + 2,
                                                motive.usages.len(),
                                                &RawTy::nat(motive.usages.len()),
                                            ),
                                        ),
                                    )
                                };
                                let mut ty_filter = filter.clone();
                                ty_filter.extend([true, true]);
                                pprint_raw_term(raw_ctx, ty_filter, &succ_inhab_ty, inner_filter, succ_inhab, f)
                            },
                            f,
                        )
                    },
                    f,
                ),
            ]);
        },

        RawStuckKind::Nat { nat } => {
            write!(f, "max[")?;
            indent(f, |f| {
                for add_all in nat.max_all.terms.iter() {
                    newline(f)?;
                    write!(f, "add[")?;
                    indent(f, |f| {
                        for (mul_all, multiplicity) in add_all.terms.iter() {
                            newline(f)?;
                            write!(f, "{} * mul[", multiplicity)?;
                            for (stuck, exponent) in mul_all.terms.iter() {
                                newline(f)?;
                                pprint_raw_stuck(raw_ctx, filter.clone(), stuck, f)?;
                                write!(f, "^{}", exponent)?;
                            }
                            newline(f)?;
                            write!(f, "]")?;
                        }
                        Ok(())
                    })?;
                    newline(f)?;
                    write!(f, "]")?;
                }
                Ok(())
            })?;
            newline(f)?;
            write!(f, "]")?;
        },

        RawStuckKind::Cong { eq_term_0, eq_term_1, elim, motive, inhab } => {
            let eq_ty = &inhab.weak.var_ty;
            let eq_ty_filter = {
                let mut eq_ty_filter = filter.clone();
                eq_ty_filter.zero_unused(&inhab.usages);
                eq_ty_filter
            };
            args!(f, "cong", [
                eq_term_0 = pprint_raw_term(raw_ctx, eq_ty_filter.clone(), &eq_ty, filter.clone(), &eq_term_0, f),
                eq_term_1 = pprint_raw_term(raw_ctx, eq_ty_filter.clone(), &eq_ty, filter.clone(), &eq_term_1, f),
                elim = pprint_raw_stuck(raw_ctx, filter.clone(), &elim, f),
                motive = pprint_raw_scope(
                    raw_ctx,
                    filter.clone(),
                    &motive,
                    |raw_ctx, inner_filter, motive, f| {
                        pprint_raw_scope(
                            raw_ctx,
                            inner_filter,
                            motive,
                            |raw_ctx, inner_filter, motive, f| {
                                pprint_raw_scope(
                                    raw_ctx,
                                    inner_filter,
                                    motive,
                                    |raw_ctx, inner_filter, motive, f| {
                                        pprint_raw_ty(raw_ctx, inner_filter, motive, f)
                                    },
                                    f,
                                )
                            },
                            f,
                        )
                    },
                    f,
                ),
                inhab = pprint_raw_scope(
                    raw_ctx,
                    filter.clone(),
                    &inhab,
                    |raw_ctx, inner_filter, inhab, f| {
                        let var_term = RawTm::var(
                            motive.usages.len() + 1,
                            motive.usages.len(),
                            &motive.weak.var_ty.clone_unfilter(&motive.usages),
                        );
                        let inhab_ty = {
                            let mut inhab_ty = motive.clone();
                            inhab_ty.weaken(1);
                            inhab_ty
                            .bind(&var_term)
                            .bind(&var_term)
                            .bind(&RawTm::refl(motive.usages.len() + 1))
                        };
                        let mut ty_filter = filter.clone();
                        ty_filter.push(true);
                        pprint_raw_term(raw_ctx, ty_filter, &inhab_ty, inner_filter, inhab, f)
                    },
                    f,
                ),
            ]);
        },

        RawStuckKind::UniqueIdentity { eq_term, elim, motive, inhab } => {
            let eq_ty = &inhab.weak.var_ty;
            let eq_ty_filter = {
                let mut eq_ty_filter = filter.clone();
                eq_ty_filter.zero_unused(&inhab.usages);
                eq_ty_filter
            };
            args!(f, "unique_identity", [
                eq_term = pprint_raw_term(raw_ctx, eq_ty_filter, eq_ty, filter.clone(), &eq_term, f),
                elim = pprint_raw_stuck(raw_ctx, filter.clone(), &elim, f),
                motive = pprint_raw_scope(
                    raw_ctx,
                    filter.clone(),
                    &motive,
                    |raw_ctx, inner_filter, motive, f| {
                        pprint_raw_scope(
                            raw_ctx,
                            inner_filter,
                            motive,
                            |raw_ctx, inner_filter, motive, f| {
                                pprint_raw_ty(raw_ctx, inner_filter, motive, f)
                            },
                            f,
                        )
                    },
                    f,
                ),
                inhab = pprint_raw_scope(
                    raw_ctx,
                    filter.clone(),
                    &inhab,
                    |raw_ctx, inner_filter, inhab, f| {
                        let var_term = RawTm::var(
                            motive.usages.len() + 1,
                            motive.usages.len(),
                            &motive.weak.var_ty.clone_unfilter(&motive.usages),
                        );
                        let inhab_ty = {
                            let mut inhab_ty = motive.clone();
                            inhab_ty.weaken(1);
                            inhab_ty
                            .bind(&var_term)
                            .bind(&RawTm::refl(motive.usages.len() + 1))
                        };
                        let mut ty_filter = filter.clone();
                        ty_filter.push(true);
                        pprint_raw_term(raw_ctx, ty_filter, &inhab_ty, inner_filter, inhab, f)
                    },
                    f,
                ),
            ]);
        },

        RawStuckKind::Explode { elim, motive } => {
            args!(f, "explode", [
                elim = pprint_raw_stuck(raw_ctx, filter.clone(), &elim, f),
                motive = pprint_raw_scope(
                    raw_ctx,
                    filter,
                    &motive,
                    |raw_ctx, inner_filter, motive, f| {
                        pprint_raw_ty(raw_ctx, inner_filter, motive, f)
                    },
                    f,
                ),
            ]);
        },

        RawStuckKind::Case { elim, motive, lhs_inhab, rhs_inhab } => {
            let lhs_ty = lhs_inhab.weak.var_ty.clone_unfilter(&lhs_inhab.usages);
            let rhs_ty = rhs_inhab.weak.var_ty.clone_unfilter(&rhs_inhab.usages);
            args!(f, "case", [
                elim = pprint_raw_stuck(raw_ctx, filter.clone(), &elim, f),
                motive = pprint_raw_scope(
                    raw_ctx,
                    filter.clone(),
                    &motive,
                    |raw_ctx, inner_filter, motive, f| {
                        pprint_raw_ty(raw_ctx, inner_filter, motive, f)
                    },
                    f,
                ),
                lhs_inhab = pprint_raw_scope(
                    raw_ctx,
                    filter.clone(),
                    &lhs_inhab,
                    |raw_ctx, inner_filter, lhs_inhab, f| {
                        let inhab_ty = {
                            let mut inhab_ty = motive.clone();
                            inhab_ty.weaken(1);
                            inhab_ty.bind(
                                &RawTm::inj_lhs(RawTm::var(
                                    motive.usages.len() + 1,
                                    motive.usages.len(),
                                    &lhs_ty,
                                )),
                            )
                        };
                        let mut ty_filter = filter.clone();
                        ty_filter.push(true);
                        pprint_raw_term(raw_ctx, ty_filter, &inhab_ty, inner_filter, lhs_inhab, f)
                    },
                    f,
                ),
                rhs_inhab = pprint_raw_scope(
                    raw_ctx,
                    filter.clone(),
                    &rhs_inhab,
                    |raw_ctx, inner_filter, rhs_inhab, f| {
                        let inhab_ty = {
                            let mut inhab_ty = motive.clone();
                            inhab_ty.weaken(1);
                            inhab_ty.bind(
                                &RawTm::inj_rhs(RawTm::var(
                                    motive.usages.len() + 1,
                                    motive.usages.len(),
                                    &rhs_ty,
                                )),
                            )
                        };
                        let mut ty_filter = filter.clone();
                        ty_filter.push(true);
                        pprint_raw_term(raw_ctx, ty_filter, &inhab_ty, inner_filter, rhs_inhab, f)
                    },
                    f,
                ),
            ]);
        },

        RawStuckKind::ProjHead { tail_ty, elim } => {
            args!(f, "proj_head", [
                tail_ty = pprint_raw_scope(
                    raw_ctx,
                    filter.clone(),
                    &tail_ty,
                    |raw_ctx, inner_filter, tail_ty, f| {
                        pprint_raw_ty(raw_ctx, inner_filter, tail_ty, f)
                    },
                    f,
                ),
                elim = pprint_raw_stuck(raw_ctx, filter.clone(), &elim, f),
            ]);
        },

        RawStuckKind::ProjTail { tail_ty, elim } => {
            args!(f, "proj_tail", [
                tail_ty = pprint_raw_scope(
                    raw_ctx,
                    filter.clone(),
                    &tail_ty,
                    |raw_ctx, inner_filter, tail_ty, f| {
                        pprint_raw_ty(raw_ctx, inner_filter, tail_ty, f)
                    },
                    f
                ),
                elim = pprint_raw_stuck(raw_ctx, filter.clone(), &elim, f),
            ]);
        },

        RawStuckKind::App { res_ty, elim, arg_term } => {
            let arg_ty = &res_ty.weak.var_ty;
            let arg_ty_filter = {
                let mut arg_ty_filter = filter.clone();
                arg_ty_filter.zero_unused(&res_ty.usages);
                arg_ty_filter
            };
            args!(f, "app", [
                res_ty = pprint_raw_scope(
                    raw_ctx,
                    filter.clone(),
                    &res_ty,
                    |raw_ctx, inner_filter, res_ty, f| {
                        pprint_raw_ty(raw_ctx, inner_filter, res_ty, f)
                    },
                    f
                ),
                elim = pprint_raw_stuck(raw_ctx, filter.clone(), &elim, f),
                arg_term = pprint_raw_term(raw_ctx, arg_ty_filter, arg_ty, filter.clone(), &arg_term, f),
            ]);
        },

        RawStuckKind::EqualEqEqTyInjective {
            eq_ty_0, eq_ty_1,
            eq_term_0_0, eq_term_0_1,
            eq_term_1_0, eq_term_1_1,
            elim,
        } => {
            args!(f, "equal_eq_eq_ty_injective", [
                eq_ty_0 = pprint_raw_ty(raw_ctx, filter.clone(), &eq_ty_0, f),
                eq_ty_1 = pprint_raw_ty(raw_ctx, filter.clone(), &eq_ty_1, f),
                eq_term_0_0 = pprint_raw_term(
                    raw_ctx, filter.clone(), &eq_ty_0, filter.clone(), &eq_term_0_0, f,
                ),
                eq_term_0_1 = pprint_raw_term(
                    raw_ctx, filter.clone(), &eq_ty_0, filter.clone(), &eq_term_0_1, f,
                ),
                eq_term_1_0 = pprint_raw_term(
                    raw_ctx, filter.clone(), &eq_ty_1, filter.clone(), &eq_term_1_0, f,
                ),
                eq_term_1_1 = pprint_raw_term(
                    raw_ctx, filter.clone(), &eq_ty_1, filter.clone(), &eq_term_1_1, f,
                ),
                elim = pprint_raw_stuck(raw_ctx, filter, &elim, f),
            ])
        },

        RawStuckKind::EqualEqEqTerm0Injective {
            eq_ty_0, eq_ty_1,
            eq_term_0_0, eq_term_0_1,
            eq_term_1_0, eq_term_1_1,
            elim,
        } => {
            args!(f, "equal_eq_eq_term_0_injective", [
                eq_ty_0 = pprint_raw_ty(raw_ctx, filter.clone(), &eq_ty_0, f),
                eq_ty_1 = pprint_raw_ty(raw_ctx, filter.clone(), &eq_ty_1, f),
                eq_term_0_0 = pprint_raw_term(
                    raw_ctx, filter.clone(), &eq_ty_0, filter.clone(), &eq_term_0_0, f,
                ),
                eq_term_0_1 = pprint_raw_term(
                    raw_ctx, filter.clone(), &eq_ty_0, filter.clone(), &eq_term_0_1, f,
                ),
                eq_term_1_0 = pprint_raw_term(
                    raw_ctx, filter.clone(), &eq_ty_1, filter.clone(), &eq_term_1_0, f,
                ),
                eq_term_1_1 = pprint_raw_term(
                    raw_ctx, filter.clone(), &eq_ty_1, filter.clone(), &eq_term_1_1, f,
                ),
                elim = pprint_raw_stuck(raw_ctx, filter, &elim, f),
            ])
        },

        RawStuckKind::EqualEqEqTerm1Injective {
            eq_ty_0, eq_ty_1,
            eq_term_0_0, eq_term_0_1,
            eq_term_1_0, eq_term_1_1,
            elim,
        } => {
            args!(f, "equal_eq_eq_term_1_injective", [
                eq_ty_0 = pprint_raw_ty(raw_ctx, filter.clone(), &eq_ty_0, f),
                eq_ty_1 = pprint_raw_ty(raw_ctx, filter.clone(), &eq_ty_1, f),
                eq_term_0_0 = pprint_raw_term(
                    raw_ctx, filter.clone(), &eq_ty_0, filter.clone(), &eq_term_0_0, f,
                ),
                eq_term_0_1 = pprint_raw_term(
                    raw_ctx, filter.clone(), &eq_ty_0, filter.clone(), &eq_term_0_1, f,
                ),
                eq_term_1_0 = pprint_raw_term(
                    raw_ctx, filter.clone(), &eq_ty_1, filter.clone(), &eq_term_1_0, f,
                ),
                eq_term_1_1 = pprint_raw_term(
                    raw_ctx, filter.clone(), &eq_ty_1, filter.clone(), &eq_term_1_1, f,
                ),
                elim = pprint_raw_stuck(raw_ctx, filter, &elim, f),
            ])
        },


        RawStuckKind::SumEqLhsInjective { lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, elim } => {
            args!(f, "sum_eq_lhs_injective", [
                lhs_ty_0 = pprint_raw_ty(raw_ctx, filter.clone(), &lhs_ty_0, f),
                lhs_ty_1 = pprint_raw_ty(raw_ctx, filter.clone(), &lhs_ty_1, f),
                rhs_ty_0 = pprint_raw_ty(raw_ctx, filter.clone(), &rhs_ty_0, f),
                rhs_ty_1 = pprint_raw_ty(raw_ctx, filter.clone(), &rhs_ty_1, f),
                elim = pprint_raw_stuck(raw_ctx, filter, &elim, f),
            ])
        },

        RawStuckKind::SumEqRhsInjective { lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, elim } => {
            args!(f, "sum_eq_rhs_injective", [
                lhs_ty_0 = pprint_raw_ty(raw_ctx, filter.clone(), &lhs_ty_0, f),
                lhs_ty_1 = pprint_raw_ty(raw_ctx, filter.clone(), &lhs_ty_1, f),
                rhs_ty_0 = pprint_raw_ty(raw_ctx, filter.clone(), &rhs_ty_0, f),
                rhs_ty_1 = pprint_raw_ty(raw_ctx, filter.clone(), &rhs_ty_1, f),
                elim = pprint_raw_stuck(raw_ctx, filter, &elim, f),
            ])
        },

        RawStuckKind::SigmaEqHeadInjective { tail_ty_0, tail_ty_1, elim } => {
            args!(f, "sigma_eq_head_injective", [
                tail_ty_0 = pprint_raw_scope(
                    raw_ctx,
                    filter.clone(),
                    &tail_ty_0,
                    |raw_ctx, filter, tail_ty_0, f| {
                        pprint_raw_ty(raw_ctx, filter, tail_ty_0, f)
                    },
                    f,
                ),
                tail_ty_1 = pprint_raw_scope(
                    raw_ctx,
                    filter.clone(),
                    &tail_ty_1,
                    |raw_ctx, filter, tail_ty_1, f| {
                        pprint_raw_ty(raw_ctx, filter, tail_ty_1, f)
                    },
                    f,
                ),
                elim = pprint_raw_stuck(raw_ctx, filter, &elim, f),
            ])
        },
        
        RawStuckKind::SigmaEqTailInjective { tail_ty_0, tail_ty_1, elim } => {
            args!(f, "sigma_eq_tail_injective", [
                tail_ty_0 = pprint_raw_scope(
                    raw_ctx,
                    filter.clone(),
                    &tail_ty_0,
                    |raw_ctx, filter, tail_ty_0, f| {
                        pprint_raw_ty(raw_ctx, filter, tail_ty_0, f)
                    },
                    f,
                ),
                tail_ty_1 = pprint_raw_scope(
                    raw_ctx,
                    filter.clone(),
                    &tail_ty_1,
                    |raw_ctx, filter, tail_ty_1, f| {
                        pprint_raw_ty(raw_ctx, filter, tail_ty_1, f)
                    },
                    f,
                ),
                elim = pprint_raw_stuck(raw_ctx, filter, &elim, f),
            ])
        },

        RawStuckKind::PiEqArgInjective { res_ty_0, res_ty_1, elim } => {
            args!(f, "pi_eq_arg_injective", [
                res_ty_0 = pprint_raw_scope(
                    raw_ctx,
                    filter.clone(),
                    &res_ty_0,
                    |raw_ctx, filter, res_ty_0, f| {
                        pprint_raw_ty(raw_ctx, filter, res_ty_0, f)
                    },
                    f,
                ),
                res_ty_1 = pprint_raw_scope(
                    raw_ctx,
                    filter.clone(),
                    &res_ty_1,
                    |raw_ctx, filter, res_ty_1, f| {
                        pprint_raw_ty(raw_ctx, filter, res_ty_1, f)
                    },
                    f,
                ),
                elim = pprint_raw_stuck(raw_ctx, filter, &elim, f),
            ])
        },
        
        RawStuckKind::PiEqResInjective { res_ty_0, res_ty_1, elim } => {
            args!(f, "pi_eq_res_injective", [
                res_ty_0 = pprint_raw_scope(
                    raw_ctx,
                    filter.clone(),
                    &res_ty_0,
                    |raw_ctx, filter, res_ty_0, f| {
                        pprint_raw_ty(raw_ctx, filter, res_ty_0, f)
                    },
                    f,
                ),
                res_ty_1 = pprint_raw_scope(
                    raw_ctx,
                    filter.clone(),
                    &res_ty_1,
                    |raw_ctx, filter, res_ty_1, f| {
                        pprint_raw_ty(raw_ctx, filter, res_ty_1, f)
                    },
                    f,
                ),
                elim = pprint_raw_stuck(raw_ctx, filter, &elim, f),
            ])
        },
    }
    Ok(())
}

fn pprint_raw_scope<S: Scheme, T>(
    raw_ctx: &RawCtx<S>,
    filter: Usages,
    raw_scope: &RawScope<S, T>,
    func: impl FnOnce(&RawCtx<S>, Usages, &Weaken<T>, &mut fmt::Formatter) -> fmt::Result,
    f: &mut fmt::Formatter,
) -> fmt::Result {
    let ctx_len = filter.len();
    let mut var_ty_filter = filter;
    var_ty_filter.zero_unused(&raw_scope.usages);
    let mut inner_filter = var_ty_filter.clone();
    inner_filter.push(true);

    let var_ty = raw_scope.var_ty_unfiltered();
    let inner_raw_ctx = raw_ctx.cons(var_ty);

    args!(f, "scope", [
        var_ty = pprint_raw_ty(raw_ctx, var_ty_filter, &raw_scope.weak.var_ty, f),
        inner = {
            write!(f, "{} |- ", ctx_len)?;
            func(&inner_raw_ctx, inner_filter, &raw_scope.weak.inner, f)?;
            Ok(())
        },
    ]);
    Ok(())
}

