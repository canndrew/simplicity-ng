use crate::priv_prelude::*;

pub type RawName<S> = Weaken<RawNameKind<S>>;

#[derive_where(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RawNameKind<S: Scheme> {
    Stuck {
        stuck: Intern<RawStuckKind<S>>,
    },
    Tag {
        tag: S::Tag,
    },
}

impl<S: Scheme> Substitute<S> for RawNameKind<S> {
    type RawSubstOutput = RawNameKind<S>;

    fn to_subst_output(&self, _num_usages: usize) -> RawNameKind<S> {
        self.clone()
    }

    fn subst(&self, filter: &Usages, var_term: RawTm<S>) -> RawName<S> {
        match self {
            RawNameKind::Stuck { stuck } => {
                RawName::from_term(stuck.subst(filter, var_term))
            },
            RawNameKind::Tag { tag } => RawName::tag(filter.len(), tag.clone()),
        }
    }

    fn eliminates_var(&self, index: usize) -> bool {
        match self {
            RawNameKind::Stuck { stuck } => stuck.eliminates_var(index),
            RawNameKind::Tag { .. } => false,
        }
    }

    fn contains_subterm(&self, subterm: RawTm<S>) -> bool {
        match self {
            RawNameKind::Stuck { stuck } => {
                stuck.contains_subterm(subterm)
            },
            RawNameKind::Tag { .. } => false,
        }
    }
}

impl<S: Scheme> RawName<S> {
    pub(crate) fn from_term(term: RawTm<S>) -> RawName<S> {
        match term.weak.get_clone() {
            RawTmKind::Stuck { stuck } => {
                let stuck = stuck.unfilter(&term.usages);
                RawName::stuck(stuck)
            },
            RawTmKind::Tag { tag } => {
                RawName::tag(term.usages.len(), tag)
            },
            _ => unreachable!(),
        }
    }

    pub(crate) fn stuck(stuck: RawStuck<S>) -> RawName<S> {
        let Weaken { usages, weak: stuck } = stuck;
        Weaken {
            usages,
            weak: RawNameKind::Stuck { stuck },
        }
    }

    pub(crate) fn tag(ctx_len: usize, tag: S::Tag) -> RawName<S> {
        Weaken {
            usages: Usages::zeros(ctx_len),
            weak: RawNameKind::Tag { tag },
        }
    }
}

