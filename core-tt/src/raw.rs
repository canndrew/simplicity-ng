use crate::priv_prelude::*;

pub(crate) trait RawContextual<N: Name> {
    type SubstOutput: RawContextual<N, SubstOutput = Self::SubstOutput> + Clone;

    fn usages(&self) -> &Usages;
    fn usages_mut(&mut self) -> &mut Usages;
    fn usages_len(&self) -> usize;
    fn clone_filter(&self, usages: &Usages) -> Self;
    fn clone_unfilter(&self, usages: &Usages) -> Self;
    fn unfilter(self, usages: &Usages) -> Self;
    fn filter_self(self) -> (Usages, Self);

    fn weaken(&mut self, ext_len: usize);
    fn clone_weaken(&self, ext_len: usize) -> Self;

    fn to_subst_output(&self) -> Self::SubstOutput;
    fn subst(&self, filter: &Usages, var_terms: &RawTm<N>) -> Self::SubstOutput;
}

#[derive(Debug, Clone, Eq)]
pub(crate) struct RawCtx<N: Name> {
    pub(crate) cons_opt: Option<Arc<RawCtxCons<N>>>,
}

impl<N: Name> PartialEq for RawCtx<N> {
    fn eq(&self, other: &RawCtx<N>) -> bool {
        match (&self.cons_opt, &other.cons_opt) {
            (None, None) => true,
            (Some(cons_0), Some(cons_1)) => Arc::ptr_eq(cons_0, cons_1),
            _ => false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RawCtxCons<N: Name> {
    pub(crate) parent: RawCtx<N>,
    pub(crate) var_name_opt: Option<N>,
    pub(crate) var_ty: RawTy<N>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct RawTy<N: Name> {
    pub(crate) usages: Usages,
    pub(crate) kind: Arc<RawTyKind<N>>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct RawTm<N: Name> {
    pub(crate) usages: Usages,
    pub(crate) kind: Arc<RawTmKind<N>>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct RawStuck<N: Name> {
    pub(crate) usages: Usages,
    pub(crate) kind: Arc<RawStuckKind<N>>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct RawScope<N: Name, T: RawContextual<N>> {
    pub(crate) usages: Usages,
    pub(crate) var_name: PhantomData<N>,
    pub(crate) var_used: bool,
    pub(crate) inner: T,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum RawTyKind<N: Name> {
    Stuck {
        stuck: RawStuck<N>,
    },
    Universe,
    Nat,
    Equal {
        eq_ty: RawTy<N>,
        eq_term_0: RawTm<N>,
        eq_term_1: RawTm<N>,
    },
    Never,
    Unit,
    Sum {
        lhs_name: N,
        lhs_ty: RawTy<N>,
        rhs_ty: RawTy<N>,
    },
    Sigma {
        head_name: N,
        head_ty: RawTy<N>,
        tail_ty: RawScope<N, RawTy<N>>,
    },
    Pi {
        arg_name: N,
        arg_ty: RawTy<N>,
        res_ty: RawScope<N, RawTy<N>>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum RawTmKind<N: Name> {
    Stuck {
        stuck: RawStuck<N>,
    },
    Type {
        ty: RawTy<N>,
    },
    Zero,
    Succs {
        count: NonZeroBigUint,
        pred_term: RawTm<N>,
    },
    Refl,
    Unit,
    InjLhs {
        lhs_term: RawTm<N>,
    },
    InjRhs {
        rhs_term: RawTm<N>,
    },
    Pair {
        head_term: RawTm<N>,
        tail_term: RawTm<N>,
    },
    Func {
        res_term: RawScope<N, RawTm<N>>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum RawStuckKind<N: Name> {
    Var,
    ForLoop {
        elim: RawStuck<N>,
        motive: RawScope<N, RawTy<N>>,
        zero_inhab: RawTm<N>,
        succ_inhab: RawScope<N, RawScope<N, RawTm<N>>>,
    },
    /*
    Max {
        max_term_0: RawStuck<N>,
        max_term_1: RawTm<N>,
    },
    */
    Cong {
        eq_ty: RawTy<N>,
        eq_term_0: RawTm<N>,
        eq_term_1: RawTm<N>,
        elim: RawStuck<N>,
        motive: RawScope<N, RawScope<N, RawScope<N, RawTy<N>>>>,
        inhab: RawScope<N, RawTm<N>>,
    },
    Explode {
        elim: RawStuck<N>,
        motive: RawScope<N, RawTy<N>>,
    },
    Relay {
        elim: RawStuck<N>,
        motive: RawScope<N, RawTy<N>>,
        inhab: RawTm<N>,
    },
    Case {
        lhs_name: N,
        lhs_ty: RawTy<N>,
        rhs_ty: RawTy<N>,
        elim: RawStuck<N>,
        motive: RawScope<N, RawTy<N>>,
        lhs_inhab: RawScope<N, RawTm<N>>,
        rhs_inhab: RawScope<N, RawTm<N>>,
    },
    Split {
        head_name: N,
        head_ty: RawTy<N>,
        tail_ty: RawScope<N, RawTy<N>>,
        elim: RawStuck<N>,
        motive: RawScope<N, RawTy<N>>,
        inhab: RawScope<N, RawScope<N, RawTm<N>>>,
    },
    App {
        arg_name: N,
        arg_ty: RawTy<N>,
        res_ty: RawScope<N, RawTy<N>>,
        elim: RawStuck<N>,
        arg_term: RawTm<N>,
    },
}

impl<N: Name> RawCtx<N> {
    pub fn root() -> RawCtx<N> {
        RawCtx {
            cons_opt: None,
        }
    }

    pub fn nth_parent(&self, n: usize) -> &RawCtx<N> {
        let mut ret = self;
        for _ in 0..n {
            let cons = ret.cons_opt.as_ref().unwrap();
            ret = &cons.parent;
        }
        ret
    }

    pub fn cons(&self, var_name_opt: Option<N>, var_ty: RawTy<N>) -> RawCtx<N> {
        RawCtx {
            cons_opt: Some(Arc::new(RawCtxCons {
                parent: self.clone(),
                var_ty,
                var_name_opt,
            })),
        }
    }
}

impl<N: Name> RawTy<N> {
    pub fn from_raw_term(term: RawTm<N>) -> RawTy<N> {
        match &*term.kind {
            RawTmKind::Stuck { stuck } => {
                let stuck = stuck.clone_unfilter(&term.usages);
                RawTy::stuck(stuck)
            },
            RawTmKind::Type { ty } => {
                let ty = ty.clone_unfilter(&term.usages);
                ty
            },
            _ => unreachable!(),
        }
    }

    pub fn stuck(mut stuck: RawStuck<N>) -> RawTy<N> {
        let usages = Usages::merge_mut([&mut stuck.usages]);

        let kind = Arc::new(RawTyKind::Stuck { stuck });
        RawTy { usages, kind }
    }

    pub fn universe(ctx_len: usize) -> RawTy<N> {
        RawTy {
            usages: Usages::zeros(ctx_len),
            kind: RawTyKind::universe(),
        }
    }

    pub fn nat(ctx_len: usize) -> RawTy<N> {
        RawTy {
            usages: Usages::zeros(ctx_len),
            kind: RawTyKind::nat(),
        }
    }

    pub fn equal(mut eq_ty: RawTy<N>, mut eq_term_0: RawTm<N>, mut eq_term_1: RawTm<N>) -> RawTy<N> {
        let usages = Usages::merge_mut([&mut eq_ty.usages, &mut eq_term_0.usages, &mut eq_term_1.usages]);

        let kind = Arc::new(RawTyKind::Equal { eq_ty, eq_term_0, eq_term_1 });
        RawTy { usages, kind }
    }

    pub fn never(ctx_len: usize) -> RawTy<N> {
        RawTy {
            usages: Usages::zeros(ctx_len),
            kind: RawTyKind::never(),
        }
    }

    pub fn unit(ctx_len: usize) -> RawTy<N> {
        RawTy {
            usages: Usages::zeros(ctx_len),
            kind: RawTyKind::unit(),
        }
    }

    pub fn sum(lhs_name: N, mut lhs_ty: RawTy<N>, mut rhs_ty: RawTy<N>) -> RawTy<N> {
        let usages = Usages::merge_mut([&mut lhs_ty.usages, &mut rhs_ty.usages]);

        let kind = Arc::new(RawTyKind::Sum { lhs_name, lhs_ty, rhs_ty });
        RawTy { usages, kind }
    }

    pub fn sigma(head_name: N, mut head_ty: RawTy<N>, mut tail_ty: RawScope<N, RawTy<N>>) -> RawTy<N> {
        let usages = Usages::merge_mut([&mut head_ty.usages, &mut tail_ty.usages]);

        let kind = Arc::new(RawTyKind::Sigma { head_name, head_ty, tail_ty });
        RawTy { usages, kind }
    }

    pub fn pi(arg_name: N, mut arg_ty: RawTy<N>, mut res_ty: RawScope<N, RawTy<N>>) -> RawTy<N> {
        let usages = Usages::merge_mut([&mut arg_ty.usages, &mut res_ty.usages]);

        let kind = Arc::new(RawTyKind::Pi { arg_name, arg_ty, res_ty });
        RawTy { usages, kind }
    }
}

impl<N: Name> RawTyKind<N> {
    pub fn universe() -> Arc<RawTyKind<N>> {
        Arc::new(RawTyKind::Universe)
    }

    pub fn nat() -> Arc<RawTyKind<N>> {
        Arc::new(RawTyKind::Nat)
    }

    pub fn never() -> Arc<RawTyKind<N>> {
        Arc::new(RawTyKind::Never)
    }

    pub fn unit() -> Arc<RawTyKind<N>> {
        Arc::new(RawTyKind::Unit)
    }
}

impl<N: Name> RawTm<N> {
    pub fn stuck(mut stuck: RawStuck<N>) -> RawTm<N> {
        let usages = Usages::merge_mut([&mut stuck.usages]);

        let kind = Arc::new(RawTmKind::Stuck { stuck });
        RawTm { usages, kind }
    }

    pub fn type_(mut ty: RawTy<N>) -> RawTm<N> {
        let usages = Usages::merge_mut([&mut ty.usages]);

        let kind = Arc::new(RawTmKind::Type { ty });
        RawTm { usages, kind }
    }

    pub fn zero(ctx_len: usize) -> RawTm<N> {
        RawTm {
            usages: Usages::zeros(ctx_len),
            kind: RawTmKind::zero(),
        }
    }

    pub fn succs(count: NonZeroBigUint, pred_term: RawTm<N>) -> RawTm<N> {
        let (count, mut pred_term) = match &*pred_term.kind {
            RawTmKind::Succs { count: other_count, pred_term: other_pred_term } => {
                let count = count + other_count;
                let pred_term = other_pred_term.clone_unfilter(&pred_term.usages);
                (count, pred_term)
            },
            _ => (count, pred_term),
        };

        let usages = Usages::merge_mut([&mut pred_term.usages]);

        let kind = Arc::new(RawTmKind::Succs { count, pred_term });
        RawTm { usages, kind }
    }

    pub fn refl(ctx_len: usize) -> RawTm<N> {
        RawTm {
            usages: Usages::zeros(ctx_len),
            kind: RawTmKind::refl(),
        }
    }

    pub fn unit(ctx_len: usize) -> RawTm<N> {
        RawTm {
            usages: Usages::zeros(ctx_len),
            kind: RawTmKind::unit(),
        }
    }

    pub fn inj_lhs(mut lhs_term: RawTm<N>) -> RawTm<N> {
        let usages = Usages::merge_mut([&mut lhs_term.usages]);

        let kind = Arc::new(RawTmKind::InjLhs { lhs_term });
        RawTm { usages, kind }
    }

    pub fn inj_rhs(mut rhs_term: RawTm<N>) -> RawTm<N> {
        let usages = Usages::merge_mut([&mut rhs_term.usages]);

        let kind = Arc::new(RawTmKind::InjRhs { rhs_term });
        RawTm { usages, kind }
    }

    pub fn pair(mut head_term: RawTm<N>, mut tail_term: RawTm<N>) -> RawTm<N> {
        let usages = Usages::merge_mut([&mut head_term.usages, &mut tail_term.usages]);

        let kind = Arc::new(RawTmKind::Pair { head_term, tail_term });
        RawTm { usages, kind }
    }

    pub fn func(mut res_term: RawScope<N, RawTm<N>>) -> RawTm<N> {
        let usages = Usages::merge_mut([&mut res_term.usages]);
        
        let kind = Arc::new(RawTmKind::Func { res_term });
        RawTm { usages, kind }
    }

    pub fn var(ctx_len: usize, index: usize) -> RawTm<N> {
        RawTm {
            usages: Usages::single_one(ctx_len, index),
            kind: RawTmKind::var(),
        }
    }

    pub fn for_loop(
        elim: RawTm<N>,
        motive: RawScope<N, RawTy<N>>,
        zero_inhab: RawTm<N>,
        succ_inhab: RawScope<N, RawScope<N, RawTm<N>>>,
    ) -> RawTm<N> {
        match &*elim.kind {
            RawTmKind::Stuck { stuck } => {
                let elim = stuck.clone_unfilter(&elim.usages);
                RawTm::stuck(RawStuck::for_loop(elim, motive, zero_inhab, succ_inhab))
            },
            RawTmKind::Zero => {
                zero_inhab
            },
            RawTmKind::Succs { count, pred_term } => {
                let pred_term = pred_term.clone_unfilter(&elim.usages);
                let pred_term = match count.try_decrement() {
                    None => pred_term,
                    Some(count) => {
                        RawTm::succs(count, pred_term)
                    },
                };
                let elim = RawTm::for_loop(pred_term.clone(), motive, zero_inhab, succ_inhab.clone());
                succ_inhab
                .bind(&pred_term)
                .bind(&elim)
            },
            _ => unreachable!(),
        }
    }

    /*
    pub fn max(
        max_term_0: RawTm<N>,
        max_term_1: RawTm<N>,
    ) -> RawTm<N> {
        match (&*max_term_0.kind, &*max_term_1.kind) {
            (RawTmKind::Zero, _) => max_term_1,
            (_, RawTmKind::Zero) => max_term_0,
            (
                RawTmKind::Succs { count: count_0, pred_term: pred_term_0 },
                RawTmKind::Succs { count: count_1, pred_term: pred_term_1 },
            ) => {
                let pred_term_0 = pred_term_0.clone_unfilter(&max_term_0.usages);
                let pred_term_1 = pred_term_1.clone_unfilter(&max_term_1.usages);
                match count_0.cmp(&count_1) {
                    cmp::Ordering::Less => {
                        let count_1 = NonZeroBigUint::new(count_1.strict_sub(count_0)).unwrap();
                        let max_term_1 = RawTm::succs(count_1, pred_term_1);
                        return RawTm::succs(count_0.clone(), RawTm::max(pred_term_0, max_term_1));
                    },
                    cmp::Ordering::Equal => {
                        return RawTm::succs(count_0.clone(), RawTm::max(pred_term_0, pred_term_1));
                    },
                    cmp::Ordering::Greater => {
                        let count_0 = NonZeroBigUint::new(count_0.strict_sub(count_1)).unwrap();
                        let max_term_0 = RawTm::succs(count_0, pred_term_0);
                        return RawTm::succs(count_1.clone(), RawTm::max(max_term_0, pred_term_1));
                    },
                }
            },
            (RawTmKind::Stuck { stuck: stuck_0 }, RawTmKind::Stuck { stuck: stuck_1 }) => {
                match stuck_0.cmp(stuck_1) {
                    cmp::Ordering::Less => {
                        RawTm::stuck(RawStuck::max(stuck_0, max_term_1))
                    },
                    cmp::Ordering::Equal => max_term_0,
                    cmp::Ordering::Greater => {
                        RawTm::stuck(RawStuck::max(stuck_1, max_term_0))
                    },
                }
            },
            (RawTmKind::Stuck { stuck }, _) => {
                RawTmKind::stuck(RawStuck::max(stuck, max_term_1))
            },
            (_, RawTmKind::Stuck { stuck }) => {
                RawTmKind::stuck(RawStuck::max(stuck, max_term_0))
            },
            _ => unreachable!(),
        }
    }
    */

    pub fn cong(
        eq_ty: RawTy<N>,
        eq_term_0: RawTm<N>,
        eq_term_1: RawTm<N>,
        elim: RawTm<N>,
        motive: RawScope<N, RawScope<N, RawScope<N, RawTy<N>>>>,
        inhab: RawScope<N, RawTm<N>>,
    ) -> RawTm<N> {
        match &*elim.kind {
            RawTmKind::Stuck { stuck } => {
                let elim = stuck.clone_unfilter(&elim.usages);
                RawTm::stuck(RawStuck::cong(eq_ty, eq_term_0, eq_term_1, elim, motive, inhab))
            },
            RawTmKind::Refl => {
                debug_assert_eq!(eq_term_0, eq_term_1);
                inhab.bind(&eq_term_0)
            },
            _ => unreachable!(),
        }
    }

    pub fn explode(
        elim: RawTm<N>,
        motive: RawScope<N, RawTy<N>>,
    ) -> RawTm<N> {
        match &*elim.kind {
            RawTmKind::Stuck { stuck } => {
                let elim = stuck.clone_unfilter(&elim.usages);
                RawTm::stuck(RawStuck::explode(elim, motive))
            },
            _ => unreachable!(),
        }
    }

    pub fn relay(
        elim: RawTm<N>,
        motive: RawScope<N, RawTy<N>>,
        inhab: RawTm<N>,
    ) -> RawTm<N> {
        match &*elim.kind {
            RawTmKind::Stuck { stuck } => {
                let elim = stuck.clone_unfilter(&elim.usages);
                RawTm::stuck(RawStuck::relay(elim, motive, inhab))
            },
            RawTmKind::Unit => {
                inhab
            },
            _ => unreachable!(),
        }
    }

    pub fn case(
        lhs_name: N,
        lhs_ty: RawTy<N>,
        rhs_ty: RawTy<N>,
        elim: RawTm<N>,
        motive: RawScope<N, RawTy<N>>,
        lhs_inhab: RawScope<N, RawTm<N>>,
        rhs_inhab: RawScope<N, RawTm<N>>,
    ) -> RawTm<N> {
        match &*elim.kind {
            RawTmKind::Stuck { stuck } => {
                let elim = stuck.clone_unfilter(&elim.usages);
                RawTm::stuck(RawStuck::case(lhs_name, lhs_ty, rhs_ty, elim, motive, lhs_inhab, rhs_inhab))
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

    pub fn split(
        head_name: N,
        head_ty: RawTy<N>,
        tail_ty: RawScope<N, RawTy<N>>,
        elim: RawTm<N>,
        motive: RawScope<N, RawTy<N>>,
        inhab: RawScope<N, RawScope<N, RawTm<N>>>,
    ) -> RawTm<N> {
        match &*elim.kind {
            RawTmKind::Stuck { stuck } => {
                let elim = stuck.clone_unfilter(&elim.usages);
                RawTm::stuck(RawStuck::split(head_name, head_ty, tail_ty, elim, motive, inhab))
            },
            RawTmKind::Pair { head_term, tail_term } => {
                let head_term = head_term.clone_unfilter(&elim.usages);
                let tail_term = tail_term.clone_unfilter(&elim.usages);
                inhab.bind2(&head_term, &tail_term)
            },
            _ => unreachable!(),
        }
    }

    pub fn app(
        arg_name: N,
        arg_ty: RawTy<N>,
        res_ty: RawScope<N, RawTy<N>>,
        elim: RawTm<N>,
        arg_term: RawTm<N>,
    ) -> RawTm<N> {
        match &*elim.kind {
            RawTmKind::Stuck { stuck } => {
                let elim = stuck.clone_unfilter(&elim.usages);
                RawTm::stuck(RawStuck::app(arg_name, arg_ty, res_ty, elim, arg_term))
            },
            RawTmKind::Func { res_term } => {
                let res_term = res_term.clone_unfilter(&elim.usages);
                res_term.bind(&arg_term)
            },
            _ => unreachable!(),
        }
    }
}

impl<N: Name> RawTmKind<N> {
    pub fn var() -> Arc<RawTmKind<N>> {
        Arc::new(RawTmKind::Stuck {
            stuck: RawStuck {
                usages: Usages::ones(1),
                kind: RawStuckKind::var(),
            },
        })
    }

    pub fn zero() -> Arc<RawTmKind<N>> {
        Arc::new(RawTmKind::Zero)
    }

    pub fn refl() -> Arc<RawTmKind<N>> {
        Arc::new(RawTmKind::Refl)
    }

    pub fn unit() -> Arc<RawTmKind<N>> {
        Arc::new(RawTmKind::Unit)
    }
}

impl<N: Name> RawStuck<N> {
    pub fn var(ctx_len: usize, index: usize) -> RawStuck<N> {
        RawStuck {
            usages: Usages::single_one(ctx_len, index),
            kind: RawStuckKind::var(),
        }
    }

    pub fn for_loop(
        mut elim: RawStuck<N>,
        mut motive: RawScope<N, RawTy<N>>,
        mut zero_inhab: RawTm<N>,
        mut succ_inhab: RawScope<N, RawScope<N, RawTm<N>>>,
    ) -> RawStuck<N> {
        let usages = Usages::merge_mut([
            &mut elim.usages,
            &mut motive.usages,
            &mut zero_inhab.usages,
            &mut succ_inhab.usages,
        ]);

        let kind = Arc::new(RawStuckKind::ForLoop { elim, motive, zero_inhab, succ_inhab });
        RawStuck { usages, kind }
    }

    /*
    pub fn max(
        max_term_0: RawStuck<N>,
        max_term_1: RawTm<N>,
    ) -> RawStuck<N> {
        if let RawStuckKind::Max { max_term_0: max_term_00, max_term_1: max_term_01 } = &*max_term_0.kind {
            let max_term_00 = max_term_00.clone_unfilter(&max_term_0.usages);
            let max_term_01 = max_term_01.clone_unfilter(&max_term_0.usages);
            return RawStuck::max(max_term_00, RawTm::max(max_term_01, max_term_1));
        }

    }
    */

    pub fn cong(
        mut eq_ty: RawTy<N>,
        mut eq_term_0: RawTm<N>,
        mut eq_term_1: RawTm<N>,
        mut elim: RawStuck<N>,
        mut motive: RawScope<N, RawScope<N, RawScope<N, RawTy<N>>>>,
        mut inhab: RawScope<N, RawTm<N>>,
    ) -> RawStuck<N> {
        let usages = Usages::merge_mut([
            &mut eq_ty.usages,
            &mut eq_term_0.usages,
            &mut eq_term_1.usages,
            &mut elim.usages,
            &mut motive.usages,
            &mut inhab.usages,
        ]);

        let kind = Arc::new(RawStuckKind::Cong { eq_ty, eq_term_0, eq_term_1, elim, motive, inhab });
        RawStuck { usages, kind }
    }

    pub fn explode(
        mut elim: RawStuck<N>,
        mut motive: RawScope<N, RawTy<N>>,
    ) -> RawStuck<N> {
        let usages = Usages::merge_mut([
            &mut elim.usages,
            &mut motive.usages,
        ]);

        let kind = Arc::new(RawStuckKind::Explode { elim, motive });
        RawStuck { usages, kind }
    }

    pub fn relay(
        mut elim: RawStuck<N>,
        mut motive: RawScope<N, RawTy<N>>,
        mut inhab: RawTm<N>,
    ) -> RawStuck<N> {
        let usages = Usages::merge_mut([
            &mut elim.usages,
            &mut motive.usages,
            &mut inhab.usages,
        ]);

        let kind = Arc::new(RawStuckKind::Relay { elim, motive, inhab });
        RawStuck { usages, kind }
    }

    pub fn case(
        lhs_name: N,
        mut lhs_ty: RawTy<N>,
        mut rhs_ty: RawTy<N>,
        mut elim: RawStuck<N>,
        mut motive: RawScope<N, RawTy<N>>,
        mut lhs_inhab: RawScope<N, RawTm<N>>,
        mut rhs_inhab: RawScope<N, RawTm<N>>,
    ) -> RawStuck<N> {
        let usages = Usages::merge_mut([
            &mut lhs_ty.usages,
            &mut rhs_ty.usages,
            &mut elim.usages,
            &mut motive.usages,
            &mut lhs_inhab.usages,
            &mut rhs_inhab.usages,
        ]);

        let kind = Arc::new(RawStuckKind::Case { lhs_name, lhs_ty, rhs_ty, elim, motive, lhs_inhab, rhs_inhab });
        RawStuck { usages, kind }
    }

    pub fn split(
        head_name: N,
        mut head_ty: RawTy<N>,
        mut tail_ty: RawScope<N, RawTy<N>>,
        mut elim: RawStuck<N>,
        mut motive: RawScope<N, RawTy<N>>,
        mut inhab: RawScope<N, RawScope<N, RawTm<N>>>,
    ) -> RawStuck<N> {
        let usages = Usages::merge_mut([
            &mut head_ty.usages,
            &mut tail_ty.usages,
            &mut elim.usages,
            &mut motive.usages,
            &mut inhab.usages,
        ]);

        let kind = Arc::new(RawStuckKind::Split { head_name, head_ty, tail_ty, elim, motive, inhab });
        RawStuck { usages, kind }
    }

    pub fn app(
        arg_name: N,
        mut arg_ty: RawTy<N>,
        mut res_ty: RawScope<N, RawTy<N>>,
        mut elim: RawStuck<N>,
        mut arg_term: RawTm<N>,
    ) -> RawStuck<N> {
        let usages = Usages::merge_mut([
            &mut arg_ty.usages,
            &mut res_ty.usages,
            &mut elim.usages,
            &mut arg_term.usages,
        ]);

        let kind = Arc::new(RawStuckKind::App { arg_name, arg_ty, res_ty ,elim, arg_term });
        RawStuck { usages, kind }
    }
}

impl<N: Name> RawStuckKind<N> {
    pub fn var() -> Arc<RawStuckKind<N>> {
        Arc::new(RawStuckKind::Var)
    }
}

impl<N: Name, T: RawContextual<N>> RawScope<N, T> {
    pub fn new(inner: T) -> RawScope<N, T> {
        let (mut usages, inner) = inner.filter_self();
        let var_used = usages.pop();
        RawScope { usages, var_name: PhantomData, var_used, inner }
    }

    pub fn bind(self, term: &RawTm<N>) -> T::SubstOutput {
        debug_assert_eq!(self.usages.len(), term.usages.len());
        let mut filter = self.usages;
        filter.push(self.var_used);
        self.inner.subst(&filter, term)
    }

    pub fn into_inner(self) -> T {
        let mut filter = self.usages;
        filter.push(self.var_used);
        self.inner.unfilter(&filter)
    }
}

impl<N: Name, T: RawContextual<N> + Clone> RawScope<N, RawScope<N, T>> {
    pub fn bind2(self, term_0: &RawTm<N>, term_1: &RawTm<N>) -> T::SubstOutput {
        self.bind(term_0).bind(term_1)
    }
}

impl<N: Name, T: RawContextual<N> + Clone> RawScope<N, RawScope<N, RawScope<N, T>>> {
    pub fn bind3(self, term_0: &RawTm<N>, term_1: &RawTm<N>, term_2: &RawTm<N>) -> T::SubstOutput {
        self.bind(term_0).bind(term_1).bind(term_2)
    }
}

impl<N: Name> RawContextual<N> for RawTy<N> {
    type SubstOutput = RawTy<N>;

    fn usages(&self) -> &Usages {
        &self.usages
    }

    fn usages_mut(&mut self) -> &mut Usages {
        &mut self.usages
    }

    fn usages_len(&self) -> usize {
        self.usages.len()
    }

    fn clone_filter(&self, usages: &Usages) -> RawTy<N> {
        RawTy {
            usages: self.usages.clone_filter(usages),
            kind: self.kind.clone(),
        }
    }

    fn clone_unfilter(&self, usages: &Usages) -> RawTy<N> {
        RawTy {
            usages: self.usages.clone_unfilter(usages),
            kind: self.kind.clone(),
        }
    }

    fn unfilter(mut self, usages: &Usages) -> RawTy<N> {
        self.usages.unfilter(usages);
        self
    }

    fn filter_self(mut self) -> (Usages, RawTy<N>) {
        let num_usages = self.usages.count_ones();
        let usages = mem::replace(&mut self.usages, Usages::ones(num_usages));
        (usages, self)
    }

    fn weaken(&mut self, ext_len: usize) {
        self.usages.weaken(ext_len);
    }

    fn clone_weaken(&self, ext_len: usize) -> RawTy<N> {
        let usages = self.usages.clone_weaken(ext_len);
        let kind = self.kind.clone();
        RawTy { usages, kind }
    }

    fn to_subst_output(&self) -> RawTy<N> {
        self.clone()
    }

    fn subst(&self, filter: &Usages, var_term: &RawTm<N>) -> RawTy<N> {
        //println!("RawTy::subst({:?}, {:?}, {:?})", self.usages, filter, var_term.usages);
        match self.usages.subst(filter, var_term) {
            ControlFlow::Break(usages) => {
                //println!("(unused)");
                RawTy {
                    usages,
                    kind: self.kind.clone(),
                }
            },
            ControlFlow::Continue((unfilter, sub_filter, var_term)) => {
                let mut ret = self.kind.subst(&sub_filter, var_term);
                ret.usages.unfilter(&unfilter);
                ret
            },
        }
    }
}

impl<N: Name> RawContextual<N> for RawTm<N> {
    type SubstOutput = RawTm<N>;

    fn usages(&self) -> &Usages {
        &self.usages
    }

    fn usages_mut(&mut self) -> &mut Usages {
        &mut self.usages
    }

    fn usages_len(&self) -> usize {
        self.usages.len()
    }

    fn clone_filter(&self, usages: &Usages) -> RawTm<N> {
        RawTm {
            usages: self.usages.clone_filter(usages),
            kind: self.kind.clone(),
        }
    }

    fn clone_unfilter(&self, usages: &Usages) -> RawTm<N> {
        RawTm {
            usages: self.usages.clone_unfilter(usages),
            kind: self.kind.clone(),
        }
    }

    fn unfilter(mut self, usages: &Usages) -> RawTm<N> {
        self.usages.unfilter(usages);
        self
    }

    fn filter_self(mut self) -> (Usages, RawTm<N>) {
        let num_usages = self.usages.count_ones();
        let usages = mem::replace(&mut self.usages, Usages::ones(num_usages));
        (usages, self)
    }

    fn weaken(&mut self, ext_len: usize) {
        self.usages.weaken(ext_len);
    }

    fn clone_weaken(&self, ext_len: usize) -> RawTm<N> {
        let usages = self.usages.clone_weaken(ext_len);
        let kind = self.kind.clone();
        RawTm { usages, kind }
    }

    fn to_subst_output(&self) -> RawTm<N> {
        self.clone()
    }

    fn subst(&self, filter: &Usages, var_term: &RawTm<N>) -> RawTm<N> {
        //println!("RawTm::subst({:?}, {:?}, {:?})", self.usages, filter, var_term.usages);
        match self.usages.subst(filter, var_term) {
            ControlFlow::Break(usages) => {
                RawTm {
                    usages,
                    kind: self.kind.clone(),
                }
            },
            ControlFlow::Continue((unfilter, sub_filter, var_term)) => {
                let mut ret = self.kind.subst(&sub_filter, var_term);
                ret.usages.unfilter(&unfilter);
                ret
            },
        }
    }
}

impl<N: Name> RawContextual<N> for RawStuck<N> {
    type SubstOutput = RawTm<N>;

    fn usages(&self) -> &Usages {
        &self.usages
    }

    fn usages_mut(&mut self) -> &mut Usages {
        &mut self.usages
    }

    fn usages_len(&self) -> usize {
        self.usages.len()
    }

    fn clone_filter(&self, usages: &Usages) -> RawStuck<N> {
        RawStuck {
            usages: self.usages.clone_filter(usages),
            kind: self.kind.clone(),
        }
    }

    fn clone_unfilter(&self, usages: &Usages) -> RawStuck<N> {
        RawStuck {
            usages: self.usages.clone_unfilter(usages),
            kind: self.kind.clone(),
        }
    }

    fn unfilter(mut self, usages: &Usages) -> RawStuck<N> {
        self.usages.unfilter(usages);
        self
    }

    fn filter_self(mut self) -> (Usages, RawStuck<N>) {
        let num_usages = self.usages.count_ones();
        let usages = mem::replace(&mut self.usages, Usages::ones(num_usages));
        (usages, self)
    }

    fn weaken(&mut self, ext_len: usize) {
        self.usages.weaken(ext_len);
    }

    fn clone_weaken(&self, ext_len: usize) -> RawStuck<N> {
        let usages = self.usages.clone_weaken(ext_len);
        let kind = self.kind.clone();
        RawStuck { usages, kind }
    }

    fn to_subst_output(&self) -> RawTm<N> {
        RawTm::stuck(self.clone())
    }

    fn subst(&self, filter: &Usages, var_term: &RawTm<N>) -> RawTm<N> {
        //println!("RawStuck::subst({:?}, {:?}, {:?})", self.usages, filter, var_term.usages);
        match self.usages.subst(filter, var_term) {
            ControlFlow::Break(usages) => {
                let stuck = RawStuck {
                    usages,
                    kind: self.kind.clone(),
                };
                RawTm::stuck(stuck)
            },
            ControlFlow::Continue((unfilter, sub_filter, var_term)) => {
                let mut ret = self.kind.subst(&sub_filter, var_term);
                ret.usages.unfilter(&unfilter);
                ret
            },
        }
    }
}

impl<N: Name, T: RawContextual<N> + Clone> RawContextual<N> for RawScope<N, T> {
    type SubstOutput = RawScope<N, T::SubstOutput>;

    fn usages(&self) -> &Usages {
        &self.usages
    }

    fn usages_mut(&mut self) -> &mut Usages {
        &mut self.usages
    }

    fn usages_len(&self) -> usize {
        self.usages.len()
    }

    fn clone_filter(&self, usages: &Usages) -> RawScope<N, T> {
        RawScope {
            usages: self.usages.clone_filter(usages),
            var_name: self.var_name.clone(),
            var_used: self.var_used,
            inner: self.inner.clone(),
        }
    }

    fn clone_unfilter(&self, usages: &Usages) -> RawScope<N, T> {
        RawScope {
            usages: self.usages.clone_unfilter(usages),
            var_name: self.var_name.clone(),
            var_used: self.var_used,
            inner: self.inner.clone(),
        }
    }

    fn unfilter(mut self, usages: &Usages) -> RawScope<N, T> {
        self.usages.unfilter(usages);
        self
    }

    fn filter_self(mut self) -> (Usages, RawScope<N, T>) {
        let num_usages = self.usages.count_ones();
        let usages = mem::replace(&mut self.usages, Usages::ones(num_usages));
        (usages, self)
    }

    fn weaken(&mut self, ext_len: usize) {
        self.usages.weaken(ext_len);
    }

    fn clone_weaken(&self, ext_len: usize) -> RawScope<N, T> {
        let usages = self.usages.clone_weaken(ext_len);
        let var_name = self.var_name.clone();
        let var_used = self.var_used;
        let inner = self.inner.clone();
        RawScope { usages, var_name, var_used, inner }
    }

    fn to_subst_output(&self) -> RawScope<N, T::SubstOutput> {
        RawScope {
            usages: self.usages.clone(),
            var_name: self.var_name.clone(),
            var_used: self.var_used,
            inner: self.inner.to_subst_output(),
        }
    }

    fn subst(&self, filter: &Usages, var_term: &RawTm<N>) -> RawScope<N, T::SubstOutput> {
        //println!("RawScope::subst({:?}, {:?}, {:?})", self.usages, filter, var_term.usages);
        match self.usages.subst(filter, var_term) {
            ControlFlow::Break(usages) => {
                RawScope {
                    usages,
                    var_name: self.var_name.clone(),
                    var_used: self.var_used,
                    inner: self.inner.to_subst_output(),
                }
            },
            ControlFlow::Continue((unfilter, mut sub_filter, var_term)) => {
                sub_filter.push(self.var_used);
                let inner = self.inner.subst(&sub_filter, &var_term);
                let mut ret = RawScope::new(inner);
                ret.usages.unfilter(&unfilter);
                ret
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RawTyped<N: Name, T> {
    pub(crate) usages: Usages,
    pub(crate) raw_ty: RawTy<N>,
    pub(crate) inner: T,
}

impl<N: Name, T: RawContextual<N> + Clone> RawContextual<N> for RawTyped<N, T> {
    type SubstOutput = RawTyped<N, T::SubstOutput>;

    fn usages(&self) -> &Usages {
        &self.usages
    }

    fn usages_mut(&mut self) -> &mut Usages {
        &mut self.usages
    }

    fn usages_len(&self) -> usize {
        self.usages.len()
    }

    fn clone_filter(&self, usages: &Usages) -> RawTyped<N, T> {
        RawTyped {
            usages: self.usages.clone_filter(usages),
            raw_ty: self.raw_ty.clone(),
            inner: self.inner.clone(),
        }
    }

    fn clone_unfilter(&self, usages: &Usages) -> RawTyped<N, T> {
        RawTyped {
            usages: self.usages.clone_unfilter(usages),
            raw_ty: self.raw_ty.clone(),
            inner: self.inner.clone(),
        }
    }

    fn unfilter(mut self, usages: &Usages) -> RawTyped<N, T> {
        self.usages.unfilter(usages);
        self
    }

    fn filter_self(mut self) -> (Usages, RawTyped<N, T>) {
        let num_usages = self.usages.count_ones();
        let usages = mem::replace(&mut self.usages, Usages::ones(num_usages));
        (usages, self)
    }

    fn weaken(&mut self, ext_len: usize) {
        self.usages.weaken(ext_len);
    }

    fn clone_weaken(&self, ext_len: usize) -> RawTyped<N, T> {
        let usages = self.usages.clone_weaken(ext_len);
        let raw_ty = self.raw_ty.clone();
        let inner = self.inner.clone();
        RawTyped { usages, raw_ty, inner }
    }

    fn to_subst_output(&self) -> RawTyped<N, T::SubstOutput> {
        let (ty, inner) = self.to_parts();
        let inner = inner.to_subst_output();
        RawTyped::from_parts(ty, inner)
    }

    fn subst(&self, filter: &Usages, var_term: &RawTm<N>) -> RawTyped<N, T::SubstOutput> {
        //println!("RawTyped::subst({:?}, {:?}, {:?})", self.usages, filter, var_term.usages);
        match self.usages.subst(filter, var_term) {
            ControlFlow::Break(usages) => {
                RawTyped {
                    usages,
                    raw_ty: self.raw_ty.clone(),
                    inner: self.inner.to_subst_output(),
                }
            },
            ControlFlow::Continue((unfilter, sub_filter, var_term)) => {
                let raw_ty = self.raw_ty.subst(&sub_filter, &var_term);
                let inner = self.inner.subst(&sub_filter, &var_term);
                let mut ret = RawTyped::from_parts(raw_ty, inner);
                ret.usages.unfilter(&unfilter);
                ret
            },
        }
    }
}

impl<N: Name, T: RawContextual<N>> RawTyped<N, T> {
    pub fn from_parts(mut raw_ty: RawTy<N>, mut inner: T) -> RawTyped<N, T> {
        let usages = Usages::merge_mut([&mut raw_ty.usages, inner.usages_mut()]);

        RawTyped { usages, raw_ty, inner }
    }

    pub fn to_parts(&self) -> (RawTy<N>, T) {
        let RawTyped { usages, raw_ty, inner } = self;
        let raw_ty = raw_ty.clone_unfilter(&usages);
        let inner = inner.clone_unfilter(&usages);
        (raw_ty, inner)
    }

    pub fn into_parts(self) -> (RawTy<N>, T) {
        let RawTyped { usages, raw_ty, inner } = self;
        let raw_ty = raw_ty.unfilter(&usages);
        let inner = inner.unfilter(&usages);
        (raw_ty, inner)
    }
}

impl<N: Name, T: RawContextual<N> + Clone> RawScope<N, RawTyped<N, T>> {
    pub fn from_parts_1(raw_ty: RawScope<N, RawTy<N>>, inner: RawScope<N, T>) -> RawScope<N, RawTyped<N, T>> {
        let raw_ty = raw_ty.into_inner();
        let inner = inner.into_inner();
        let inner = RawTyped::from_parts(raw_ty, inner);
        RawScope::new(inner)
    }

    pub fn into_parts(self) -> (RawScope<N, RawTy<N>>, RawScope<N, T>) {
        let inner = self.into_inner();
        let (raw_ty, inner) = inner.into_parts();
        let raw_ty = RawScope::new(raw_ty);
        let inner = RawScope::new(inner);
        (raw_ty, inner)
    }
}

impl<N: Name, T: RawContextual<N> + Clone> RawScope<N, RawScope<N, RawTyped<N, T>>> {
    /*
    pub fn from_parts_2(raw_ty: RawScope<N, RawTy<N>>, inner: RawScope<N, T>) -> RawScope<N, RawTyped<N, T>> {
        let raw_ty = raw_ty.into_inner();
        let inner = inner.into_inner();
        let inner = RawTyped::from_parts(raw_ty, inner);
        RawScope::new(inner)
    }
    */

    pub fn into_parts(self) -> (RawScope<N, RawScope<N, RawTy<N>>>, RawScope<N, RawScope<N, T>>) {
        let inner = self.into_inner();
        let inner = inner.into_inner();
        let (raw_ty, inner) = inner.into_parts();
        let raw_ty = RawScope::new(RawScope::new(raw_ty));
        let inner = RawScope::new(RawScope::new(inner));
        (raw_ty, inner)
    }
}

impl<N: Name> RawTyKind<N> {
    fn subst(self: &Arc<RawTyKind<N>>, filter: &Usages, var_term: RawTm<N>) -> RawTy<N> {
        match &**self {
            RawTyKind::Stuck { stuck } => {
                let stuck = stuck.subst(filter, &var_term);
                RawTy::from_raw_term(stuck)
            },
            RawTyKind::Universe => RawTy::universe(filter.len()),
            RawTyKind::Nat => RawTy::nat(filter.len()),
            RawTyKind::Equal { eq_ty, eq_term_0, eq_term_1 } => {
                let eq_ty = eq_ty.subst(filter, &var_term);
                let eq_term_0 = eq_term_0.subst(filter, &var_term);
                let eq_term_1 = eq_term_1.subst(filter, &var_term);
                RawTy::equal(eq_ty, eq_term_0, eq_term_1)
            },
            RawTyKind::Never => RawTy::never(filter.len()),
            RawTyKind::Unit => RawTy::unit(filter.len()),
            RawTyKind::Sum { lhs_name, lhs_ty, rhs_ty } => {
                let lhs_ty = lhs_ty.subst(filter, &var_term);
                let rhs_ty = rhs_ty.subst(filter, &var_term);
                RawTy::sum(lhs_name.clone(), lhs_ty, rhs_ty)
            },
            RawTyKind::Sigma { head_name, head_ty, tail_ty } => {
                let head_ty = head_ty.subst(filter, &var_term);
                let tail_ty = tail_ty.subst(filter, &var_term);
                RawTy::sigma(head_name.clone(), head_ty, tail_ty)
            },
            RawTyKind::Pi { arg_name, arg_ty, res_ty } => {
                let arg_ty = arg_ty.subst(filter, &var_term);
                let res_ty = res_ty.subst(filter, &var_term);
                RawTy::pi(arg_name.clone(), arg_ty, res_ty)
            },
        }
    }
}

impl<N: Name> RawTmKind<N> {
    fn subst(self: &Arc<RawTmKind<N>>, filter: &Usages, var_term: RawTm<N>) -> RawTm<N> {
        match &**self {
            RawTmKind::Stuck { stuck } => {
                stuck.subst(filter, &var_term)
            },
            RawTmKind::Type { ty } => {
                let ty = ty.subst(filter, &var_term);
                RawTm::type_(ty)
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
            RawTmKind::Pair { head_term, tail_term } => {
                let head_term = head_term.subst(filter, &var_term);
                let tail_term = tail_term.subst(filter, &var_term);
                RawTm::pair(head_term, tail_term)
            },
            RawTmKind::Func { res_term } => {
                let res_term = res_term.subst(filter, &var_term);
                RawTm::func(res_term)
            },
        }
    }
}

impl<N: Name> RawStuckKind<N> {
    fn subst(self: &Arc<RawStuckKind<N>>, filter: &Usages, var_term: RawTm<N>) -> RawTm<N> {
        match &**self {
            RawStuckKind::Var => {
                let mut var_term = var_term;
                var_term.weaken(filter.len().strict_sub(1).strict_sub(var_term.usages.len()));
                var_term
            },

            RawStuckKind::ForLoop { elim, motive, zero_inhab, succ_inhab } => {
                let elim = elim.subst(filter, &var_term);
                let motive = motive.subst(filter, &var_term);
                let zero_inhab = zero_inhab.subst(filter, &var_term);
                let succ_inhab = succ_inhab.subst(filter, &var_term);
                RawTm::for_loop(elim, motive, zero_inhab, succ_inhab)
            },

            /*
            RawStuckKind::Max { max_term_0, max_term_1 } => {
                let max_term_0 = max_term_0.subst(filter, &var_term);
                let max_term_1 = max_term_1.subst(filter, &var_term);
                RawTm::max(max_term_0, max_term_1)
            },
            */

            RawStuckKind::Cong { eq_ty, eq_term_0, eq_term_1, elim, motive, inhab } => {
                let eq_ty = eq_ty.subst(filter, &var_term);
                let eq_term_0 = eq_term_0.subst(filter, &var_term);
                let eq_term_1 = eq_term_1.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                let motive = motive.subst(filter, &var_term);
                let inhab = inhab.subst(filter, &var_term);
                RawTm::cong(eq_ty, eq_term_0, eq_term_1, elim, motive, inhab)
            },

            RawStuckKind::Explode { elim, motive } => {
                let elim = elim.subst(filter, &var_term);
                let motive = motive.subst(filter, &var_term);
                RawTm::explode(elim, motive)
            },

            RawStuckKind::Relay { elim, motive, inhab } => {
                let elim = elim.subst(filter, &var_term);
                let motive = motive.subst(filter, &var_term);
                let inhab = inhab.subst(filter, &var_term);
                RawTm::relay(elim, motive, inhab)
            },

            RawStuckKind::Case { lhs_name, lhs_ty, rhs_ty, elim, motive, lhs_inhab, rhs_inhab } => {
                let lhs_ty = lhs_ty.subst(filter, &var_term);
                let rhs_ty = rhs_ty.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                let motive = motive.subst(filter, &var_term);
                let lhs_inhab = lhs_inhab.subst(filter, &var_term);
                let rhs_inhab = rhs_inhab.subst(filter, &var_term);
                RawTm::case(lhs_name.clone(), lhs_ty, rhs_ty, elim, motive, lhs_inhab, rhs_inhab)
            },

            RawStuckKind::Split { head_name, head_ty, tail_ty, elim, motive, inhab } => {
                let head_ty = head_ty.subst(filter, &var_term);
                let tail_ty = tail_ty.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                let motive = motive.subst(filter, &var_term);
                let inhab = inhab.subst(filter, &var_term);
                RawTm::split(head_name.clone(), head_ty, tail_ty, elim, motive, inhab)
            },

            RawStuckKind::App { arg_name, arg_ty, res_ty, elim, arg_term } => {
                let arg_ty = arg_ty.subst(filter, &var_term);
                let res_ty = res_ty.subst(filter, &var_term);
                let elim = elim.subst(filter, &var_term);
                let arg_term = arg_term.subst(filter, &var_term);
                RawTm::app(arg_name.clone(), arg_ty, res_ty, elim, arg_term)
            },
        }
    }
}

