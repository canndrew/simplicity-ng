use crate::priv_prelude::*;
use std::collections::HashSet;

#[derive(Debug)]
pub struct Stats<N: Name> {
    tys: HashSet<usize>,
    terms: HashSet<usize>,
    stucks: HashSet<usize>,
    num_tys: usize,
    num_terms: usize,
    num_stucks: usize,
    num_unique_tys: usize,
    num_unique_terms: usize,
    num_unique_stucks: usize,
}

impl<N: Name> Stats<N> {
    pub fn new() -> Stats<N> {
        Stats {
            tys: HashSet::new(),
            terms: HashSet::new(),
            stucks: HashSet::new(),
            num_tys: 0,
            num_terms: 0,
            num_stucks: 0,
            num_unique_tys: 0,
            num_unique_terms: 0,
            num_unique_stucks: 0,
        }
    }

    pub fn print(&self) {
        println!("num_tys == {}; unique == {}", self.num_tys, self.num_unique_tys);
        println!("num_terms == {}; unique == {}", self.num_terms, self.num_unique_terms);
        println!("num_stucks == {}; unique == {}", self.num_stucks, self.num_unique_stucks);
    }
}

pub trait CollectStats<N: Name> {
    fn collect_stats(&self, stats: &mut Stats<N>);
}

impl<N: Name> CollectStats<N> for RawTy<N> {
    fn collect_stats(&self, stats: &mut Stats<N>) {
        self.kind.collect_stats(stats);
    }
}

impl<N: Name> CollectStats<N> for RawTm<N> {
    fn collect_stats(&self, stats: &mut Stats<N>) {
        self.kind.collect_stats(stats);
    }
}

impl<N: Name> CollectStats<N> for RawStuck<N> {
    fn collect_stats(&self, stats: &mut Stats<N>) {
        self.kind.collect_stats(stats);
    }
}

impl<N: Name> Intern<RawTyKind<N>> {
    fn collect_stats(self, stats: &mut Stats<N>) {
        stats.num_tys += 1;
        if stats.tys.insert(Arc::as_ptr(self)) {
            stats.num_unique_tys += 1;
        }
        match self.get().kind() {
            RawTyKind::Stuck { stuck } => stuck.collect_stats(stats),
            RawTyKind::Universe => (),
            RawTyKind::Nat => (),
            RawTyKind::Equal { eq_ty, eq_term_0, eq_term_1 } => {
                eq_ty.collect_stats(stats);
                eq_term_0.collect_stats(stats);
                eq_term_1.collect_stats(stats);
            },
            RawTyKind::Never => (),
            RawTyKind::Unit => (),
            RawTyKind::Sum { lhs_name: _, lhs_ty, rhs_ty } => {
                lhs_ty.collect_stats(stats);
                rhs_ty.collect_stats(stats);
            },
            RawTyKind::Sigma { tail_ty } => {
                tail_ty.collect_stats(stats);
            },
            RawTyKind::Pi { res_ty } => {
                res_ty.collect_stats(stats);
            },
        }
    }
}

impl<N: Name> RawTmKind<N> {
    fn collect_stats(self: &Arc<RawTmKind<N>>, stats: &mut Stats<N>) {
        stats.num_terms += 1;
        if stats.terms.insert(Arc::as_ptr(self)) {
            stats.num_unique_terms += 1;
        }
        match &**self {
            RawTmKind::Stuck { stuck } => stuck.collect_stats(stats),
            RawTmKind::Type { ty } => ty.collect_stats(stats),
            RawTmKind::Zero => (),
            RawTmKind::Succs { count: _, pred_term } => {
                pred_term.collect_stats(stats);
            },
            RawTmKind::Refl => (),
            RawTmKind::Unit => (),
            RawTmKind::InjLhs { lhs_term } => {
                lhs_term.collect_stats(stats);
            },
            RawTmKind::InjRhs { rhs_term } => {
                rhs_term.collect_stats(stats);
            },
            RawTmKind::Pair { head_name: _, head_term, tail_term } => {
                head_term.collect_stats(stats);
                tail_term.collect_stats(stats);
            },
            RawTmKind::Func { res_term } => {
                res_term.collect_stats(stats);
            },
        }
    }
}

impl<N: Name> RawStuckKind<N> {
    fn collect_stats(self: &Arc<RawStuckKind<N>>, stats: &mut Stats<N>) {
        stats.num_stucks += 1;
        if stats.stucks.insert(Arc::as_ptr(self)) {
            stats.num_unique_stucks += 1;
        }
        match &**self {
            RawStuckKind::Var => (),
            RawStuckKind::ForLoop { elim, motive, zero_inhab, succ_inhab } => {
                elim.collect_stats(stats);
                motive.collect_stats(stats);
                zero_inhab.collect_stats(stats);
                succ_inhab.collect_stats(stats);
            },
            RawStuckKind::Nat { nat } => nat.collect_stats(stats),
            RawStuckKind::Cong { eq_term_0, eq_term_1, elim, motive, inhab } => {
                eq_term_0.collect_stats(stats);
                eq_term_1.collect_stats(stats);
                elim.collect_stats(stats);
                motive.collect_stats(stats);
                inhab.collect_stats(stats);
            },
            RawStuckKind::UniqueIdentity { eq_term, elim, motive, inhab } => {
                eq_term.collect_stats(stats);
                elim.collect_stats(stats);
                motive.collect_stats(stats);
                inhab.collect_stats(stats);
            },
            RawStuckKind::Explode { elim, motive } => {
                elim.collect_stats(stats);
                motive.collect_stats(stats);
            },
            RawStuckKind::Case { elim, motive, lhs_inhab, rhs_inhab } => {
                elim.collect_stats(stats);
                motive.collect_stats(stats);
                lhs_inhab.collect_stats(stats);
                rhs_inhab.collect_stats(stats);
            },
            RawStuckKind::ProjHead { tail_ty, elim } => {
                tail_ty.collect_stats(stats);
                elim.collect_stats(stats);
            },
            RawStuckKind::ProjTail { tail_ty, elim } => {
                tail_ty.collect_stats(stats);
                elim.collect_stats(stats);
            },
            RawStuckKind::App { res_ty, elim, arg_term } => {
                res_ty.collect_stats(stats);
                elim.collect_stats(stats);
                arg_term.collect_stats(stats);
            },
        }
    }
}

impl<N: Name, T: RawContextual<N> + CollectStats<N>> CollectStats<N> for RawScope<N, T> {
    fn collect_stats(&self, stats: &mut Stats<N>) {
        self.var_ty.collect_stats(stats);
        self.inner.collect_stats(stats);
    }
}

impl<N: Name, T: RawContextual<N> + CollectStats<N>> CollectStats<N> for RawAnonScope<N, T> {
    fn collect_stats(&self, stats: &mut Stats<N>) {
        self.var_ty.collect_stats(stats);
        self.inner.collect_stats(stats);
    }
}

impl<N: Name> Nat<N> {
    fn collect_stats(&self, stats: &mut Stats<N>) {
        for term in self.iter_terms() {
            term.collect_stats(stats);
        }
    }
}

impl<N: Name, T: RawContextual<N> + CollectStats<N>> CollectStats<N> for RawTyped<N, T> {
    fn collect_stats(&self, stats: &mut Stats<N>) {
        self.raw_ty.collect_stats(stats);
        self.inner.collect_stats(stats);
    }
}

impl<N: Name, T: Contextual<N>> CollectStats<N> for Scope<N, T>
where
    T::Raw: RawContextual<N> + CollectStats<N>,
{
    fn collect_stats(&self, stats: &mut Stats<N>) {
        self.raw_scope.collect_stats(stats);
    }
}

