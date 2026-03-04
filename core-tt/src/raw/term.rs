use crate::priv_prelude::*;

pub type RawTm<S> = Weaken<Intern<RawTmKind<S>>>;

#[derive_where(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RawTmKind<S: Scheme> {
    Stuck {
        stuck: RawStuck<S>,
    },
    Tag {
        tag: S::Tag,
    },
    Type {
        ty: RawTy<S>,
    },
    Zero,
    Succs {
        count: NonZeroBigUint,
        pred_term: RawTm<S>,
    },
    Refl,
    Unit,
    InjLhs {
        lhs_term: RawTm<S>,
    },
    InjRhs {
        rhs_term: RawTm<S>,
    },
    Pair {
        head_name: RawName<S>,
        head_term: RawTm<S>,
        tail_term: RawTm<S>,
    },
    Func {
        arg_name: RawName<S>,
        res_term: RawScope<S, Intern<RawTmKind<S>>>,
    },
}

impl<S: Scheme> RawTm<S> {
    pub(crate) fn stuck(mut stuck: RawStuck<S>) -> RawTm<S> {
        let usages = Usages::merge_mut([&mut stuck.usages]);

        let weak = Intern::new(RawTmKind::Stuck { stuck });
        Weaken { usages, weak }
    }

    pub(crate) fn tag(ctx_len: usize, tag: S::Tag) -> RawTm<S> {
        Weaken {
            usages: Usages::zeros(ctx_len),
            weak: RawTmKind::tag(tag),
        }
    }

    pub(crate) fn from_name(name: RawName<S>) -> RawTm<S> {
        let Weaken { usages, weak: name } = name;
        match name {
            RawNameKind::Stuck { stuck } => {
                let stuck = Weaken { usages, weak: stuck };
                RawTm::stuck(stuck)
            },
            RawNameKind::Tag { tag } => {
                RawTm::tag(usages.len(), tag)
            },
        }
    }

    pub(crate) fn from_ty(mut ty: RawTy<S>) -> RawTm<S> {
        if let RawTyKind::Stuck { stuck } = ty.weak.get_clone() {
            let stuck = stuck.clone_unfilter(&ty.usages);
            return RawTm::stuck(stuck);
        }

        let usages = Usages::merge_mut([&mut ty.usages]);

        let weak = Intern::new(RawTmKind::Type { ty });
        Weaken { usages, weak }
    }

    pub(crate) fn zero(ctx_len: usize) -> RawTm<S> {
        Weaken {
            usages: Usages::zeros(ctx_len),
            weak: RawTmKind::zero(),
        }
    }

    pub(crate) fn succs(count: NonZeroBigUint, pred_term: RawTm<S>) -> RawTm<S> {
        let (count, mut pred_term) = match pred_term.weak.get_clone() {
            RawTmKind::Succs { count: other_count, pred_term: other_pred_term } => {
                let count = count + other_count;
                let pred_term = other_pred_term.clone_unfilter(&pred_term.usages);
                (count, pred_term)
            },
            _ => (count, pred_term),
        };

        let usages = Usages::merge_mut([&mut pred_term.usages]);

        let weak = Intern::new(RawTmKind::Succs { count, pred_term });
        Weaken { usages, weak }
    }

    pub(crate) fn one(ctx_len: usize) -> RawTm<S> {
        RawTm::succs(NonZeroBigUint::new(BigUint::from(1usize)).unwrap(), RawTm::zero(ctx_len))
    }

    pub(crate) fn from_constant(ctx_len: usize, val: BigUint) -> RawTm<S> {
        RawNat::from_constant(ctx_len, val).into_raw_term()
    }

    pub(crate) fn max(lhs: RawTm<S>, rhs: RawTm<S>) -> RawTm<S> {
        let lhs = RawNat::from_raw_term(lhs);
        let rhs = RawNat::from_raw_term(rhs);
        RawNat::max(lhs, rhs).into_raw_term()
    }

    pub(crate) fn add(lhs: RawTm<S>, rhs: RawTm<S>) -> RawTm<S> {
        let lhs = RawNat::from_raw_term(lhs);
        let rhs = RawNat::from_raw_term(rhs);
        RawNat::add(lhs, rhs).into_raw_term()
    }

    pub(crate) fn mul(lhs: RawTm<S>, rhs: RawTm<S>) -> RawTm<S> {
        let lhs = RawNat::from_raw_term(lhs);
        let rhs = RawNat::from_raw_term(rhs);
        RawNat::mul(lhs, rhs).into_raw_term()
    }

    pub(crate) fn mul_constant_non_zero(self, val: &NonZeroBigUint) -> RawTm<S> {
        let nat = RawNat::from_raw_term(self);
        nat.mul_constant_non_zero(val).into_raw_term()
    }

    pub(crate) fn pow_constant_non_zero(self, val: &NonZeroBigUint) -> RawTm<S> {
        let nat = RawNat::from_raw_term(self);
        let ret = nat.pow_constant(val.clone().into_big_uint());
        let ret = ret.into_raw_term();
        ret
    }

    pub(crate) fn refl(ctx_len: usize) -> RawTm<S> {
        Weaken {
            usages: Usages::zeros(ctx_len),
            weak: RawTmKind::refl(),
        }
    }

    pub(crate) fn unit(ctx_len: usize) -> RawTm<S> {
        Weaken {
            usages: Usages::zeros(ctx_len),
            weak: RawTmKind::unit(),
        }
    }

    pub(crate) fn inj_lhs(mut lhs_term: RawTm<S>) -> RawTm<S> {
        let usages = Usages::merge_mut([&mut lhs_term.usages]);

        let weak = Intern::new(RawTmKind::InjLhs { lhs_term });
        Weaken { usages, weak }
    }

    pub(crate) fn inj_rhs(mut rhs_term: RawTm<S>) -> RawTm<S> {
        let usages = Usages::merge_mut([&mut rhs_term.usages]);

        let weak = Intern::new(RawTmKind::InjRhs { rhs_term });
        Weaken { usages, weak }
    }

    pub(crate) fn pair(
        mut head_name: RawName<S>,
        mut head_term: RawTm<S>,
        mut tail_term: RawTm<S>,
    ) -> RawTm<S> {
        if let RawTmKind::Stuck { stuck } = head_term.weak.get_clone()
        && let RawStuckKind::ProjHead {
            head_name: elim_head_name, elim: head_elim, tail_ty: elim_tail_ty,
        } = stuck.weak.get_clone()
        && head_name == elim_head_name.unfilter(&head_term.usages)
        {
            if let RawTmKind::Stuck { stuck } = tail_term.weak.get_clone()
            && let RawStuckKind::ProjTail { elim: tail_elim, .. } = stuck.weak.get_clone()
            && let Some(elim) = as_equal(
                head_elim.clone_unfilter(&head_term.usages),
                tail_elim.unfilter(&tail_term.usages),
            ) {
                return RawTm::stuck(elim);
            }

            let elim_tail_ty = {
                elim_tail_ty
                .clone_unfilter(&head_term.usages)
            };
            if let Some(eta_tail_term) = elim_tail_ty.unique_eta_term_opt(&mut Vec::new()) {
                // Still not 100% sure this is sound.
                // If you ever get stack overflows from infinite recursion then this is prolly it.
                let eta_tail_term = eta_tail_term.bind(&head_term);
                if tail_term == eta_tail_term {
                    let ret = head_elim.unfilter(&head_term.usages);
                    return RawTm::stuck(ret);
                }
            }


            /*
            // This won't infinitely recurse but it's an incomplete check and can lead to
            // non-preservation of typing.

            let elim_tail_ty = {
                let mut filter = elim_tail_ty.usages.clone_unfilter(&head_term.usages);
                filter.push(true);
                elim_tail_ty.weak.inner.unfilter(&filter)
            };
            if tail_term.clone_weaken(1).is_unique_eta_term_for_type(&elim_tail_ty) {
                let ret = head_elim.clone_unfilter(&head_term.usages);
                return RawTm::stuck(ret);
            }
            */
        }

        if let RawTmKind::Stuck { stuck } = tail_term.weak.get_clone()
        && let RawStuckKind::ProjTail {
            head_name: elim_head_name, elim: tail_elim, tail_ty: elim_tail_ty,
        } = stuck.weak.get_clone()
        && head_name == elim_head_name.unfilter(&tail_term.usages)
        && head_term.is_unique_eta_term_for_type(
            &elim_tail_ty
            .var_ty_unfiltered()
            .unfilter(&tail_term.usages)
        ) {
            let ret = tail_elim.clone_unfilter(&tail_term.usages);
            return RawTm::stuck(ret);
        }

        let usages = Usages::merge_mut([
            &mut head_name.usages, &mut head_term.usages, &mut tail_term.usages,
        ]);

        let weak = Intern::new(RawTmKind::Pair { head_name, head_term, tail_term });
        Weaken { usages, weak }
    }

    pub(crate) fn func(
        mut arg_name: RawName<S>,
        mut res_term: RawScope<S, Intern<RawTmKind<S>>>,
    ) -> RawTm<S> {
        if let RawTmKind::Stuck { stuck } = res_term.weak.inner.weak.get_clone()
        && let RawStuckKind::App {
            arg_name: app_arg_name, res_ty: _, elim, arg_term,
        } = stuck.weak.get_clone()
        {
            let mut app_arg_name = app_arg_name.unfilter(&res_term.weak.inner.usages);
            if !app_arg_name.usages.pop()
            && arg_name == app_arg_name.unfilter(&res_term.usages)
            {
                if res_term.var_used()
                && !elim.usages.last()
                && arg_term.usages.is_single(arg_term.usages.len().strict_sub(1))
                && let RawTmKind::Stuck { stuck } = arg_term.weak.get_clone()
                && let RawStuckKind::Var = stuck.weak.get_clone()
                {
                    let mut ret = elim.clone_unfilter(&res_term.weak.inner.usages);
                    ret.usages.pop();
                    let ret = ret.unfilter(&res_term.usages);
                    return RawTm::stuck(ret);
                }

                if !res_term.var_used()
                && {
                    let mut arg_term = arg_term.clone_unfilter(&res_term.weak.inner.usages);
                    assert!(!arg_term.usages.pop());
                    arg_term.is_unique_eta_term_for_type(&res_term.weak.var_ty)
                }
                {
                    let ret = elim.clone();
                    let ret = ret.unfilter(&res_term.usages);
                    return RawTm::stuck(ret);
                }
            }
        }

        let usages = Usages::merge_mut([&mut arg_name.usages, &mut res_term.usages]);
        
        let weak = Intern::new(RawTmKind::Func { arg_name, res_term });
        Weaken { usages, weak }
    }

    pub(crate) fn var(ctx_len: usize, index: usize, var_ty: &RawTy<S>) -> RawTm<S> {
        debug_assert_eq!(index, var_ty.usages.len());
        if let Some(eta_term) = var_ty.unique_eta_term_opt(&mut Vec::new()) {
            debug_assert_eq!(eta_term.usages.len(), index);
            return eta_term.weaken(ctx_len.strict_sub(index));
        }
        Weaken {
            usages: Usages::single_one(ctx_len, index),
            weak: RawTmKind::var(),
        }
    }

    pub(crate) fn for_loop(
        elim: RawTm<S>,
        motive: RawScope<S, Intern<RawTyKind<S>>>,
        zero_inhab: RawTm<S>,
        succ_inhab: RawScope<S, RawScopeKind<S, Intern<RawTmKind<S>>>>,
    ) -> RawTm<S> {
        match elim.weak.get_clone() {
            RawTmKind::Stuck { stuck } => {
                let elim = stuck.clone_unfilter(&elim.usages);
                RawTm::stuck(RawStuck::for_loop(elim, motive, zero_inhab, succ_inhab))
            },
            RawTmKind::Zero => {
                zero_inhab
            },
            RawTmKind::Succs { count, pred_term } => {
                let pred_term = pred_term.clone_unfilter(&elim.usages);
                let mut state = {
                    succ_inhab
                    .clone()
                    .bind(&pred_term)
                    .bind(&RawTm::for_loop(
                        pred_term.clone(),
                        motive.clone(),
                        zero_inhab.clone(),
                        succ_inhab.clone(),
                    ))
                };
                let mut succs = NonZeroBigUint::one();
                while succs != count {
                    let pred_term = RawTm::succs(succs.clone(), pred_term.clone());
                    state = {
                        succ_inhab
                        .clone()
                        .bind(&pred_term)
                        .bind(&state)
                    };
                    succs += 1;
                }
                state
            },
            _ => unreachable!(),
        }
    }

    pub(crate) fn cong(
        eq_term_0: RawTm<S>,
        eq_term_1: RawTm<S>,
        elim: RawTm<S>,
        motive: RawScope<S, RawScopeKind<S, RawScopeKind<S, Intern<RawTyKind<S>>>>>,
        inhab: RawScope<S, Intern<RawTmKind<S>>>,
    ) -> RawTm<S> {
        match elim.weak.get_clone() {
            RawTmKind::Stuck { stuck } => {
                let elim = stuck.clone_unfilter(&elim.usages);
                RawTm::stuck(RawStuck::cong(eq_term_0, eq_term_1, elim, motive, inhab))
            },
            RawTmKind::Refl => {
                debug_assert_eq!(eq_term_0, eq_term_1);
                inhab.bind(&eq_term_0)
            },
            _ => unreachable!(),
        }
    }

    pub(crate) fn unique_identity(
        eq_term: RawTm<S>,
        elim: RawTm<S>,
        motive: RawScope<S, RawScopeKind<S, Intern<RawTyKind<S>>>>,
        inhab: RawScope<S, Intern<RawTmKind<S>>>,
    ) -> RawTm<S> {
        match elim.weak.get_clone() {
            RawTmKind::Stuck { stuck } => {
                let elim = stuck.clone_unfilter(&elim.usages);
                RawTm::stuck(RawStuck::unique_identity(eq_term, elim, motive, inhab))
            },
            RawTmKind::Refl => {
                inhab.bind(&eq_term)
            },
            _ => unreachable!(),
        }
    }

    pub(crate) fn explode(
        elim: RawTm<S>,
        motive: RawScope<S, Intern<RawTyKind<S>>>,
    ) -> RawTm<S> {
        match elim.weak.get_clone() {
            RawTmKind::Stuck { stuck } => {
                let elim = stuck.clone_unfilter(&elim.usages);
                RawTm::stuck(RawStuck::explode(elim, motive))
            },
            _ => unreachable!(),
        }
    }

    pub(crate) fn case(
        lhs_name: RawName<S>,
        elim: RawTm<S>,
        motive: RawScope<S, Intern<RawTyKind<S>>>,
        lhs_inhab: RawScope<S, Intern<RawTmKind<S>>>,
        rhs_inhab: RawScope<S, Intern<RawTmKind<S>>>,
    ) -> RawTm<S> {
        match elim.weak.get_clone() {
            RawTmKind::Stuck { stuck } => {
                let elim = stuck.clone_unfilter(&elim.usages);
                RawTm::stuck(RawStuck::case(lhs_name, elim, motive, lhs_inhab, rhs_inhab))
            },
            RawTmKind::InjLhs { lhs_term } => {
                let lhs_term = lhs_term.clone_unfilter(&elim.usages);
                lhs_inhab.bind(&lhs_term)
            },
            RawTmKind::InjRhs { rhs_term } => {
                let rhs_term = rhs_term.clone_unfilter(&elim.usages);
                rhs_inhab.bind(&rhs_term)
            },
            _ => unreachable!(),
        }
    }

    pub(crate) fn proj_head(
        head_name: RawName<S>,
        tail_ty: RawScope<S, Intern<RawTyKind<S>>>,
        elim: RawTm<S>,
    ) -> RawTm<S> {
        match elim.weak.get_clone() {
            RawTmKind::Stuck { stuck } => {
                let elim = stuck.clone_unfilter(&elim.usages);
                RawTm::stuck(RawStuck::proj_head(head_name, tail_ty, elim))
            },
            RawTmKind::Pair { head_name: term_head_name, head_term, tail_term: _ } => {
                debug_assert_eq!(head_name, term_head_name.clone_unfilter(&elim.usages));
                head_term.clone_unfilter(&elim.usages)
            },
            _ => unreachable!(),
        }
    }

    pub(crate) fn proj_tail(
        head_name: RawName<S>,
        tail_ty: RawScope<S, Intern<RawTyKind<S>>>,
        elim: RawTm<S>,
    ) -> RawTm<S> {
        match elim.weak.get_clone() {
            RawTmKind::Stuck { stuck } => {
                let elim = stuck.clone_unfilter(&elim.usages);
                RawTm::stuck(RawStuck::proj_tail(head_name, tail_ty, elim))
            },
            RawTmKind::Pair { head_name: term_head_name, head_term: _, tail_term } => {
                debug_assert_eq!(head_name, term_head_name.clone_unfilter(&elim.usages));
                tail_term.clone_unfilter(&elim.usages)
            },
            _ => unreachable!(),
        }
    }

    pub(crate) fn app(
        arg_name: RawName<S>,
        res_ty: RawScope<S, Intern<RawTyKind<S>>>,
        elim: RawTm<S>,
        arg_term: RawTm<S>,
    ) -> RawTm<S> {
        match elim.weak.get_clone() {
            RawTmKind::Stuck { stuck } => {
                let elim = stuck.clone_unfilter(&elim.usages);
                RawTm::stuck(RawStuck::app(arg_name, res_ty, elim, arg_term))
            },
            RawTmKind::Func { arg_name: func_arg_name, res_term } => {
                debug_assert_eq!(arg_name, func_arg_name.unfilter(&elim.usages));
                let res_term = res_term.clone_unfilter(&elim.usages);
                res_term.bind(&arg_term)
            },
            _ => unreachable!(),
        }
    }

    pub(crate) fn unique_eta_term_opt(
        &self,
        ty_var_etas: &mut Vec<(usize, usize)>,
    ) -> Option<RawTm<S>> {
        match self.weak.get_clone() {
            RawTmKind::Stuck { stuck } => {
                let term = stuck.unique_eta_term_opt(ty_var_etas)?;
                Some(term.unfilter(&self.usages))
            },
            RawTmKind::Type { ty } => {
                let term = ty.unique_eta_term_opt(ty_var_etas)?;
                Some(term.unfilter(&self.usages))
            },
            _ => unreachable!(),
        }
    }

    pub(crate) fn is_unique_eta_term_for_type(&self, ty: &RawTy<S>) -> bool {
        debug_assert_eq!(self.usages.len(), ty.usages.len());
        match self.weak.get_clone() {
            RawTmKind::Stuck { stuck } => {
                if true {
                    // hanging? disable for now.
                    return false;
                }
                stuck.unfilter(&self.usages).is_unique_eta_term_for_type(ty)
            },

            RawTmKind::Tag { .. } |
            RawTmKind::Type { .. } |
            RawTmKind::Zero |
            RawTmKind::Succs { .. } |
            RawTmKind::Refl |
            RawTmKind::InjLhs { .. } |
            RawTmKind::InjRhs { .. } => false,

            RawTmKind::Unit => {
                let RawTyKind::Unit = ty.weak.get_clone() else {
                    return false;
                };
                true
            },

            RawTmKind::Pair { head_name, head_term, tail_term } => {
                let RawTyKind::Sigma {
                    head_name: ty_head_name, tail_ty,
                } = ty.weak.get_clone() else {
                    return false;
                };
                if head_name.unfilter(&self.usages) != ty_head_name.unfilter(&ty.usages) {
                    return false;
                }
                if {
                    head_term
                    .unfilter(&self.usages)
                    .is_unique_eta_term_for_type(
                        &tail_ty
                        .var_ty_unfiltered()
                        .unfilter(&ty.usages),
                    )
                } {
                    debug_assert!(!tail_ty.var_used());
                    tail_term
                    .unfilter(&self.usages)
                    .is_unique_eta_term_for_type(
                        &tail_ty
                        .inner_unfiltered_strengthen()
                        .unfilter(&ty.usages),
                    )
                } else {
                    false
                }
            },

            RawTmKind::Func { arg_name, res_term } => {
                let RawTyKind::Pi { arg_name: ty_arg_name, res_ty } = ty.weak.get_clone() else {
                    return false;
                };

                arg_name.unfilter(&self.usages) == ty_arg_name.unfilter(&ty.usages) 
                && {
                    let (res_term_inner, res_term_var_ty) = res_term.into_inner();
                    let (res_ty_inner, res_ty_var_ty) = res_ty.into_inner();
                    res_term_var_ty == res_ty_var_ty &&
                    res_term_inner.is_unique_eta_term_for_type(&res_ty_inner)
                }
            },
        }
    }

    pub(crate) fn tags_apart(
        tag_0: S::Tag,
        tag_1: S::Tag,
        elim: RawTm<S>,
    ) -> RawTm<S> {
        match elim.weak.get_clone() {
            RawTmKind::Stuck { stuck } => {
                let elim = stuck.clone_unfilter(&elim.usages);
                RawTm::stuck(RawStuck::tags_apart(tag_0, tag_1, elim))
            },
            _ => unreachable!(),
        }
    }

    pub(crate) fn equal_eq_eq_ty_injective(
        eq_ty_0: RawTy<S>,
        eq_ty_1: RawTy<S>,
        eq_term_0_0: RawTm<S>,
        eq_term_0_1: RawTm<S>,
        eq_term_1_0: RawTm<S>,
        eq_term_1_1: RawTm<S>,
        elim: RawTm<S>,
    ) -> RawTm<S> {
        match elim.weak.get_clone() {
            RawTmKind::Stuck { stuck } => {
                let elim = stuck.clone_unfilter(&elim.usages);
                RawTm::stuck(RawStuck::equal_eq_eq_ty_injective(
                    eq_ty_0, eq_ty_1,
                    eq_term_0_0, eq_term_0_1,
                    eq_term_1_0, eq_term_1_1,
                    elim,
                ))
            },
            RawTmKind::Refl => {
                debug_assert_eq!(eq_ty_0, eq_ty_1);
                debug_assert_eq!(eq_term_0_0, eq_term_0_1);
                debug_assert_eq!(eq_term_1_0, eq_term_1_1);
                elim
            },
            _ => unreachable!(),
        }
    }

    pub(crate) fn equal_eq_eq_term_0_injective(
        eq_ty: RawTy<S>,
        eq_term_0_0: RawTm<S>,
        eq_term_0_1: RawTm<S>,
        eq_term_1_0: RawTm<S>,
        eq_term_1_1: RawTm<S>,
        elim: RawTm<S>,
    ) -> RawTm<S> {
        match elim.weak.get_clone() {
            RawTmKind::Stuck { stuck } => {
                let elim = stuck.clone_unfilter(&elim.usages);
                RawTm::stuck(RawStuck::equal_eq_eq_term_0_injective(
                    eq_ty,
                    eq_term_0_0, eq_term_0_1,
                    eq_term_1_0, eq_term_1_1,
                    elim,
                ))
            },
            RawTmKind::Refl => {
                debug_assert_eq!(eq_term_0_0, eq_term_0_1);
                debug_assert_eq!(eq_term_1_0, eq_term_1_1);
                elim
            },
            _ => unreachable!(),
        }
    }

    pub(crate) fn equal_eq_eq_term_1_injective(
        eq_ty: RawTy<S>,
        eq_term_0_0: RawTm<S>,
        eq_term_0_1: RawTm<S>,
        eq_term_1_0: RawTm<S>,
        eq_term_1_1: RawTm<S>,
        elim: RawTm<S>,
    ) -> RawTm<S> {
        match elim.weak.get_clone() {
            RawTmKind::Stuck { stuck } => {
                let elim = stuck.clone_unfilter(&elim.usages);
                RawTm::stuck(RawStuck::equal_eq_eq_term_1_injective(
                    eq_ty,
                    eq_term_0_0, eq_term_0_1,
                    eq_term_1_0, eq_term_1_1,
                    elim,
                ))
            },
            RawTmKind::Refl => {
                debug_assert_eq!(eq_term_0_0, eq_term_0_1);
                debug_assert_eq!(eq_term_1_0, eq_term_1_1);
                elim
            },
            _ => unreachable!(),
        }
    }

    pub(crate) fn sum_eq_name_injective(
        lhs_name_0: RawName<S>,
        lhs_name_1: RawName<S>,
        lhs_ty_0: RawTy<S>,
        lhs_ty_1: RawTy<S>,
        rhs_ty_0: RawTy<S>,
        rhs_ty_1: RawTy<S>,
        elim: RawTm<S>,
    ) -> RawTm<S> {
        match elim.weak.get_clone() {
            RawTmKind::Stuck { stuck } => {
                let elim = stuck.clone_unfilter(&elim.usages);
                RawTm::stuck(RawStuck::sum_eq_name_injective(
                    lhs_name_0, lhs_name_1, lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, elim,
                ))
            },
            RawTmKind::Refl => {
                debug_assert_eq!(lhs_name_0, lhs_name_1);
                debug_assert_eq!(lhs_ty_0, lhs_ty_1);
                debug_assert_eq!(rhs_ty_0, rhs_ty_1);
                elim
            },
            _ => unreachable!(),
        }
    }

    pub(crate) fn sum_eq_lhs_injective(
        lhs_name_0: RawName<S>,
        lhs_name_1: RawName<S>,
        lhs_ty_0: RawTy<S>,
        lhs_ty_1: RawTy<S>,
        rhs_ty_0: RawTy<S>,
        rhs_ty_1: RawTy<S>,
        elim: RawTm<S>,
    ) -> RawTm<S> {
        match elim.weak.get_clone() {
            RawTmKind::Stuck { stuck } => {
                let elim = stuck.clone_unfilter(&elim.usages);
                RawTm::stuck(RawStuck::sum_eq_lhs_injective(
                    lhs_name_0, lhs_name_1, lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, elim,
                ))
            },
            RawTmKind::Refl => {
                debug_assert_eq!(lhs_name_0, lhs_name_1);
                debug_assert_eq!(lhs_ty_0, lhs_ty_1);
                debug_assert_eq!(rhs_ty_0, rhs_ty_1);
                elim
            },
            _ => unreachable!(),
        }
    }

    pub(crate) fn sum_eq_rhs_injective(
        lhs_name_0: RawName<S>,
        lhs_name_1: RawName<S>,
        lhs_ty_0: RawTy<S>,
        lhs_ty_1: RawTy<S>,
        rhs_ty_0: RawTy<S>,
        rhs_ty_1: RawTy<S>,
        elim: RawTm<S>,
    ) -> RawTm<S> {
        match elim.weak.get_clone() {
            RawTmKind::Stuck { stuck } => {
                let elim = stuck.clone_unfilter(&elim.usages);
                RawTm::stuck(RawStuck::sum_eq_rhs_injective(
                    lhs_name_0, lhs_name_1, lhs_ty_0, lhs_ty_1, rhs_ty_0, rhs_ty_1, elim,
                ))
            },
            RawTmKind::Refl => {
                debug_assert_eq!(lhs_name_0, lhs_name_1);
                debug_assert_eq!(lhs_ty_0, lhs_ty_1);
                debug_assert_eq!(rhs_ty_0, rhs_ty_1);
                elim
            },
            _ => unreachable!(),
        }
    }

    pub(crate) fn sigma_eq_name_injective(
        head_name_0: RawName<S>,
        head_name_1: RawName<S>,
        tail_ty_0: RawScope<S, Intern<RawTyKind<S>>>,
        tail_ty_1: RawScope<S, Intern<RawTyKind<S>>>,
        elim: RawTm<S>,
    ) -> RawTm<S> {
        match elim.weak.get_clone() {
            RawTmKind::Stuck { stuck } => {
                let elim = stuck.clone_unfilter(&elim.usages);
                RawTm::stuck(RawStuck::sigma_eq_name_injective(
                    head_name_0, head_name_1, tail_ty_0, tail_ty_1, elim,
                ))
            },
            RawTmKind::Refl => {
                debug_assert_eq!(head_name_0, head_name_1);
                debug_assert_eq!(tail_ty_0, tail_ty_1);
                elim
            },
            _ => unreachable!(),
        }
    }

    pub(crate) fn sigma_eq_head_injective(
        head_name_0: RawName<S>,
        head_name_1: RawName<S>,
        tail_ty_0: RawScope<S, Intern<RawTyKind<S>>>,
        tail_ty_1: RawScope<S, Intern<RawTyKind<S>>>,
        elim: RawTm<S>,
    ) -> RawTm<S> {
        match elim.weak.get_clone() {
            RawTmKind::Stuck { stuck } => {
                let elim = stuck.clone_unfilter(&elim.usages);
                RawTm::stuck(RawStuck::sigma_eq_head_injective(
                    head_name_0, head_name_1, tail_ty_0, tail_ty_1, elim,
                ))
            },
            RawTmKind::Refl => {
                debug_assert_eq!(head_name_0, head_name_1);
                debug_assert_eq!(tail_ty_0, tail_ty_1);
                elim
            },
            _ => unreachable!(),
        }
    }

    pub(crate) fn sigma_eq_tail_injective(
        head_name: RawName<S>,
        tail_ty_0: RawScope<S, Intern<RawTyKind<S>>>,
        tail_ty_1: RawScope<S, Intern<RawTyKind<S>>>,
        elim: RawTm<S>,
    ) -> RawTm<S> {
        match elim.weak.get_clone() {
            RawTmKind::Stuck { stuck } => {
                let elim = stuck.clone_unfilter(&elim.usages);
                RawTm::stuck(RawStuck::sigma_eq_tail_injective(
                    head_name,
                    tail_ty_0,
                    tail_ty_1,
                    elim,
                ))
            },
            RawTmKind::Refl => {
                debug_assert_eq!(tail_ty_0, tail_ty_1);
                elim
            },
            _ => unreachable!(),
        }
    }

    pub(crate) fn pi_eq_name_injective(
        arg_name_0: RawName<S>,
        arg_name_1: RawName<S>,
        res_ty_0: RawScope<S, Intern<RawTyKind<S>>>,
        res_ty_1: RawScope<S, Intern<RawTyKind<S>>>,
        elim: RawTm<S>,
    ) -> RawTm<S> {
        match elim.weak.get_clone() {
            RawTmKind::Stuck { stuck } => {
                let elim = stuck.clone_unfilter(&elim.usages);
                RawTm::stuck(RawStuck::pi_eq_name_injective(
                    arg_name_0, arg_name_1, res_ty_0, res_ty_1, elim,
                ))
            },
            RawTmKind::Refl => {
                debug_assert_eq!(arg_name_0, arg_name_1);
                debug_assert_eq!(res_ty_0, res_ty_1);
                elim
            },
            _ => unreachable!(),
        }
    }

    pub(crate) fn pi_eq_arg_injective(
        arg_name_0: RawName<S>,
        arg_name_1: RawName<S>,
        res_ty_0: RawScope<S, Intern<RawTyKind<S>>>,
        res_ty_1: RawScope<S, Intern<RawTyKind<S>>>,
        elim: RawTm<S>,
    ) -> RawTm<S> {
        match elim.weak.get_clone() {
            RawTmKind::Stuck { stuck } => {
                let elim = stuck.clone_unfilter(&elim.usages);
                RawTm::stuck(RawStuck::pi_eq_arg_injective(
                    arg_name_0, arg_name_1, res_ty_0, res_ty_1, elim,
                ))
            },
            RawTmKind::Refl => {
                debug_assert_eq!(arg_name_0, arg_name_1);
                debug_assert_eq!(res_ty_0, res_ty_1);
                elim
            },
            _ => unreachable!(),
        }
    }

    pub(crate) fn pi_eq_res_injective(
        arg_name: RawName<S>,
        res_ty_0: RawScope<S, Intern<RawTyKind<S>>>,
        res_ty_1: RawScope<S, Intern<RawTyKind<S>>>,
        elim: RawTm<S>,
    ) -> RawTm<S> {
        match elim.weak.get_clone() {
            RawTmKind::Stuck { stuck } => {
                let elim = stuck.clone_unfilter(&elim.usages);
                RawTm::stuck(RawStuck::pi_eq_res_injective(
                    arg_name,
                    res_ty_0,
                    res_ty_1, 
                    elim, 
                ))
            },
            RawTmKind::Refl => {
                debug_assert_eq!(res_ty_0, res_ty_1);
                elim
            },
            _ => unreachable!(),
        }
    }
}

impl<S: Scheme> RawTmKind<S> {
    pub(crate) fn var() -> Intern<RawTmKind<S>> {
        Intern::new(RawTmKind::Stuck {
            stuck: RawStuck::var(1, 0),
        })
    }

    pub(crate) fn tag(tag: S::Tag) -> Intern<RawTmKind<S>> {
        Intern::new(RawTmKind::Tag { tag })
    }

    pub(crate) fn zero() -> Intern<RawTmKind<S>> {
        Intern::new(RawTmKind::Zero)
    }

    pub(crate) fn refl() -> Intern<RawTmKind<S>> {
        Intern::new(RawTmKind::Refl)
    }

    pub(crate) fn unit() -> Intern<RawTmKind<S>> {
        Intern::new(RawTmKind::Unit)
    }
}


impl<S: Scheme> Substitute<S> for Intern<RawTmKind<S>> {
    type RawSubstOutput = Intern<RawTmKind<S>>;

    fn to_subst_output(&self, _num_usages: usize) -> Intern<RawTmKind<S>> {
        self.clone()
    }

    fn subst(&self, filter: &Usages, var_term: RawTm<S>) -> RawTm<S> {
        match self.get_clone() {
            RawTmKind::Stuck { stuck } => {
                stuck.subst(filter, &var_term)
            },
            RawTmKind::Tag { tag } => {
                RawTm::tag(filter.len(), tag)
            },
            RawTmKind::Type { ty } => {
                let ty = ty.subst(filter, &var_term);
                RawTm::from_ty(ty)
            },
            RawTmKind::Zero => RawTm::zero(filter.len()),
            RawTmKind::Succs { count, pred_term } => {
                let pred_term = pred_term.subst(filter, &var_term);
                RawTm::succs(count.clone(), pred_term)
            },
            RawTmKind::Refl => RawTm::refl(filter.len()),
            RawTmKind::Unit => RawTm::unit(filter.len()),
            RawTmKind::InjLhs { lhs_term } => {
                let lhs_term = lhs_term.subst(filter, &var_term);
                RawTm::inj_lhs(lhs_term)
            },
            RawTmKind::InjRhs { rhs_term } => {
                let rhs_term = rhs_term.subst(filter, &var_term);
                RawTm::inj_rhs(rhs_term)
            },
            RawTmKind::Pair { head_name, head_term, tail_term } => {
                let head_name = head_name.subst(filter, &var_term);
                let head_term = head_term.subst(filter, &var_term);
                let tail_term = tail_term.subst(filter, &var_term);
                RawTm::pair(head_name, head_term, tail_term)
            },
            RawTmKind::Func { arg_name, res_term } => {
                let arg_name = arg_name.subst(filter, &var_term);
                let res_term = res_term.subst(filter, &var_term);
                RawTm::func(arg_name, res_term)
            },
        }
    }

    fn eliminates_var(&self, index: usize) -> bool {
        match self.get_clone() {
            RawTmKind::Stuck { stuck } => stuck.eliminates_var(index),
            RawTmKind::Tag { .. } => false,
            RawTmKind::Type { ty } => ty.eliminates_var(index),
            RawTmKind::Zero => false,
            RawTmKind::Succs { count: _, pred_term } => pred_term.eliminates_var(index),
            RawTmKind::Refl => false,
            RawTmKind::Unit => false,
            RawTmKind::InjLhs { lhs_term } => lhs_term.eliminates_var(index),
            RawTmKind::InjRhs { rhs_term } => rhs_term.eliminates_var(index),
            RawTmKind::Pair { head_name, head_term, tail_term } => {
                head_name.eliminates_var(index) ||
                head_term.eliminates_var(index) ||
                tail_term.eliminates_var(index)
            },
            RawTmKind::Func { arg_name, res_term } => {
                arg_name.eliminates_var(index) &&
                res_term.eliminates_var(index)
            },
        }
    }

    fn contains_subterm(&self, subterm: RawTm<S>) -> bool {
        if self.get_index() < subterm.weak.get_index() {
            return false;
        }
        if subterm.usages.is_ones() && self.get_index() == subterm.weak.get_index() {
            return true;
        }
        match self.get_clone() {
            RawTmKind::Stuck { stuck } => {
                stuck.contains_subterm(&subterm)
            },
            RawTmKind::Type { ty } => {
                ty.contains_subterm(&subterm)
            },
            RawTmKind::Succs { pred_term, .. } => {
                pred_term.contains_subterm(&subterm)
            },
            RawTmKind::InjLhs { lhs_term } => {
                lhs_term.contains_subterm(&subterm)
            },
            RawTmKind::InjRhs { rhs_term } => {
                rhs_term.contains_subterm(&subterm)
            },
            RawTmKind::Pair { head_name, head_term, tail_term } => {
                head_name.contains_subterm(&subterm) ||
                head_term.contains_subterm(&subterm) ||
                tail_term.contains_subterm(&subterm)
            },
            RawTmKind::Func { arg_name, res_term } => {
                arg_name.contains_subterm(&subterm) ||
                res_term.contains_subterm(&subterm)
            },

            RawTmKind::Tag { .. } |
            RawTmKind::Zero |
            RawTmKind::Refl |
            RawTmKind::Unit => false,
        }
    }
}

