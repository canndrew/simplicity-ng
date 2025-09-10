use crate::priv_prelude::*;

#[derive_where(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RawNat<S: Scheme> {
    pub(crate) usages: Usages,
    pub(crate) max_all: MaxAll<S>,
}

#[derive_where(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct MaxAll<S: Scheme> {
    pub(crate) terms: OrdSet<AddAll<S>>,
}

#[derive_where(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct AddAll<S: Scheme> {
    pub(crate) terms: OrdMap<MulAll<S>, NonZeroBigUint>,
}

#[derive_where(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct MulAll<S: Scheme> {
    pub(crate) terms: OrdMap<RawStuck<S>, NonZeroBigUint>,
}

impl<S: Scheme> RawNat<S> {
    pub fn zero(ctx_len: usize) -> RawNat<S> {
        RawNat {
            usages: Usages::zeros(ctx_len),
            max_all: MaxAll::zero(),
        }
    }

    pub fn one(ctx_len: usize) -> RawNat<S> {
        RawNat {
            usages: Usages::zeros(ctx_len),
            max_all: MaxAll::one(),
        }
    }

    pub fn succs(self, count: &NonZeroBigUint) -> RawNat<S> {
        let RawNat { usages, max_all } = self;
        let max_all = max_all.succs(count);
        RawNat { usages, max_all }
    }

    pub fn max(mut lhs: RawNat<S>, mut rhs: RawNat<S>) -> RawNat<S> {
        let usages = Usages::merge_mut([&mut lhs.usages, &mut rhs.usages]);
        let lhs = lhs.max_all.unfilter(&lhs.usages);
        let rhs = rhs.max_all.unfilter(&rhs.usages);
        RawNat {
            usages,
            max_all: MaxAll::max(lhs, rhs),
        }
    }

    pub fn add(mut lhs: RawNat<S>, mut rhs: RawNat<S>) -> RawNat<S> {
        let usages = Usages::merge_mut([&mut lhs.usages, &mut rhs.usages]);
        let lhs = lhs.max_all.unfilter(&lhs.usages);
        let rhs = rhs.max_all.unfilter(&rhs.usages);

        RawNat {
            usages,
            max_all: MaxAll::add(&lhs, &rhs),
        }
    }

    pub fn mul(mut lhs: RawNat<S>, mut rhs: RawNat<S>) -> RawNat<S> {
        let usages = Usages::merge_mut([&mut lhs.usages, &mut rhs.usages]);
        let lhs = lhs.max_all.unfilter(&lhs.usages);
        let rhs = rhs.max_all.unfilter(&rhs.usages);

        RawNat {
            usages,
            max_all: MaxAll::mul(&lhs, &rhs),
        }
    }

    pub fn mul_constant_non_zero(self, n: &NonZeroBigUint) -> RawNat<S> {
        let max_all = self.max_all.mul_non_zero_constant(n);
        RawNat { usages: self.usages, max_all }
    }

    pub fn pow_constant(self, n: BigUint) -> RawNat<S> {
        let mut ret = RawNat::one(self.usages.len());
        let mut self_pow_pow_2 = self;
        let mut n = n;
        loop {
            if n.is_zero() {
                break;
            }
            if n.bit(0) {
                ret = RawNat::mul(ret, self_pow_pow_2.clone());
            }
            n >>= 1u32;
            if n.is_zero() {
                break;
            }
            self_pow_pow_2 = RawNat::mul(self_pow_pow_2.clone(), self_pow_pow_2);
        }
        ret
    }

    pub fn from_constant(ctx_len: usize, val: BigUint) -> RawNat<S> {
        match NonZeroBigUint::new(val) {
            None => RawNat::zero(ctx_len),
            Some(val) => RawNat::from_constant_non_zero(ctx_len, val),
        }
    }

    pub fn from_constant_non_zero(ctx_len: usize, val: NonZeroBigUint) -> RawNat<S> {
        RawNat {
            usages: Usages::zeros(ctx_len),
            max_all: MaxAll::from_constant_non_zero(val),
        }
    }

    pub fn from_raw_term(term: RawTm<S>) -> RawNat<S> {
        match term.weak.get_clone() {
            RawTmKind::Zero => RawNat::zero(term.usages.len()),
            RawTmKind::Succs { count, pred_term } => {
                let pred_term = pred_term.clone_unfilter(&term.usages);
                RawNat::add(
                    RawNat::from_constant_non_zero(term.usages.len(), count.clone()),
                    RawNat::from_raw_term(pred_term),
                )
            },
            RawTmKind::Stuck { stuck } => {
                let stuck = stuck.clone_unfilter(&term.usages);
                RawNat::from_stuck(stuck)
            },
            _ => unreachable!(),
        }
    }

    pub fn from_stuck(stuck: RawStuck<S>) -> RawNat<S> {
        match stuck.weak.get_clone() {
            RawStuckKind::Nat { nat } => {
                let nat = nat.clone_unfilter(&stuck.usages);
                nat
            },
            _ => {
                let (usages, stuck) = stuck.filter_self();
                let max_all = MaxAll::from_stuck(stuck);
                RawNat { usages, max_all }
            },
        }
    }

    pub fn is_zero(&self) -> bool {
        self.max_all.is_zero()
    }

    pub fn succs_count(&self) -> BigUint {
        self.max_all.succs_count()
    }

    pub fn strict_sub_constant(&self, val: &BigUint) -> RawNat<S> {
        match NonZeroBigUint::new(val.clone()) {
            None => self.clone(),
            Some(val) => {
                let max_all = self.max_all.strict_sub_non_zero_constant(&val);
                RawNat {
                    usages: self.usages.clone(),
                    max_all,
                }
            },
        }
    }

    /*
    pub fn try_decrement(&self) -> Option<RawNat<S>> {
        let max_all = self.max_all.try_decrement()?;
        Some(RawNat {
            usages: self.usages.clone(),
            max_all,
        })
    }

    pub fn is_single_term(&self) -> bool {
        self.max_all.is_single_term()
    }

    pub fn into_single_term(self) -> RawStuck<S> {
        let mut term = self.max_all.into_single_term();
        term.usages_mut().unfilter(&self.usages);
        term
    }
    */

    pub fn iter_terms(&self) -> impl Iterator<Item = &RawStuck<S>> {
        self.max_all.iter_terms()
    }

    /*
    pub fn try_map_inner<F, E>(&self, target_len: usize, mut func: F) -> Result<RawTm<S>, E>
    where
        F: FnMut(&RawStuck<S>) -> Result<RawTm<S>, E>,
    {
        self.max_all.try_map_inner(target_len, &mut func)
    }

    pub fn map_inner<F>(&self, target_len: usize, mut func: F) -> RawTm<S>
    where
        F: FnMut(&RawStuck<S>) -> RawTm<S>,
    {
        let res: Result<_, !> = self.try_map_inner(target_len, |term| Ok(func(term)));
        let Ok(term_opt) = res;
        term_opt
    }
    */

    /*
    pub fn unfilter(mut self, usages: &Usages) -> RawNat<S> {
        self.usages.unfilter(usages);
        self
    }
    */

    pub fn clone_unfilter(&self, usages: &Usages) -> RawNat<S> {
        RawNat {
            usages: self.usages.clone_unfilter(usages),
            max_all: self.max_all.clone(),
        }
    }

    /*
    pub fn initial(&self) -> RawStuck<S> {
        self.iter_terms().next().expect("initial() called on constant RawNat").clone()
    }
    */

    pub fn into_raw_term(self) -> RawTm<S> {
        if self.max_all.terms.len() == 1 {
            let mut add_all = self.max_all.terms.into_iter().next().unwrap();
            if add_all.terms.is_empty() {
                RawTm::zero(self.usages.len())
            } else {
                let succs_opt = add_all.terms.remove(&MulAll::one());
                let stuck = if add_all.is_single_term() {
                    let stuck = add_all.into_single_term();
                    stuck.unfilter(&self.usages)
                } else {
                    RawStuck::nat(RawNat {
                        usages: self.usages,
                        max_all: MaxAll {
                            terms: ordset! { add_all },
                        },
                    })
                };
                let term = RawTm::stuck(stuck);
                match succs_opt {
                    None => term,
                    Some(count) => {
                        RawTm::succs(count, term)
                    },
                }
            }
        } else {
            let mut iter = self.max_all.terms.iter();
            let add_all = iter.next().unwrap();
            let mut min_succs_opt = add_all.terms.get(&MulAll::one());
            while let Some(min_succs) = &min_succs_opt && let Some(add_all) = iter.next() {
                match add_all.terms.get(&MulAll::one()) {
                    None => min_succs_opt = None,
                    Some(count) => {
                        if count < min_succs {
                            min_succs_opt = Some(count);
                        }
                    },
                }
            }
            match min_succs_opt {
                None => {
                    RawTm::stuck(RawStuck::nat(self))
                },
                Some(succs) => {
                    let succs = succs.clone();
                    let mut terms = OrdSet::new();
                    for mut add_all in self.max_all.terms.into_iter() {
                        let count = add_all.terms.remove(&MulAll::one()).unwrap();
                        let new_count = count.strict_sub(&succs);
                        if let Some(new_count) = NonZeroBigUint::new(new_count) {
                            add_all.terms.insert(MulAll::one(), new_count);
                        }
                        terms.insert(add_all);
                    }
                    let term = RawTm::stuck(RawStuck::nat(RawNat {
                        usages: self.usages,
                        max_all: MaxAll { terms },
                    }));
                    RawTm::succs(succs, term)
                },
            }
        }
    }

    pub fn subst(&self, filter: &Usages, var_term: &RawTm<S>) -> RawTm<S> {
        /*
        debug!("calling RawNat::subst on:");
        debug_indent!(("max"), {
            for add_all in self.max_all.terms.iter() {
                debug_indent!(("add"), {
                    for (mul_all, multiplicity) in add_all.terms.iter() {
                        debug_indent!(("{} * mul", multiplicity), {
                            let mut first = true;
                            for (stuck, exponent) in mul_all.terms.iter() {
                                if !first {
                                    debug!(" * {:?}^{}", stuck, exponent);
                                } else {
                                    first = false;
                                    debug!("{:?}^{}", stuck, exponent);
                                }
                            }
                        });
                    }
                });
            }
        });
        */
        
        match self.usages.subst(filter, var_term) {
            ControlFlow::Break(usages) => {
                let nat = RawNat {
                    usages,
                    max_all: self.max_all.clone(),
                };
                let stuck = RawStuck::nat(nat);
                RawTm::stuck(stuck)
            },
            ControlFlow::Continue((unfilter, sub_filter, var_term)) => {
                let mut ret = self.max_all.subst(&sub_filter, &var_term);
                ret.usages.unfilter(&unfilter);
                ret
            },
        }
    }

    /*
    pub(crate) fn map_scheme<V: Scheme>(
        &self,
        map_user_ty: &mut impl FnMut(&S::UserTy) -> V::UserTy,
        map_user_term: &mut impl FnMut(&S::UserTm) -> V::UserTm,
    ) -> RawNat<V> {
        let RawNat { usages, max_all } = self;
        let usages = usages.clone();
        let max_all = max_all.map_scheme(map_user_ty, map_user_term);
        RawNat { usages, max_all }
    }
    */

    /*
    pub fn extract_succs(&self) -> (BigUint, Option<RawNat<S>>) {
        let mut add_alls = self.max_all.iter();
        let add_all = add_alls.next().unwrap();

        if self.max_all.len() == 1 {
            match add_all.terms.get(&MulAll::one()) {
                None => return (BigUint::zero(), None),
                Some(count) => {
                    if add_all.len() == 1 {
                        return (count.clone().into_big_uint(), None);
                    }
                },
            }
            match add_all.terms.iter().next() {
                None => return (BigUint::zero(), None),
                Some((mul_all, multiplicity)) => {
                    if add_all.len() == 1 {
                        if mul_all.terms.len() == 0 {

                        }
                    }
                },
            }
            if add_all.len() == 0 {
                return (BigUint::zero(), None);
            }
            let (mul_all, multiplicity) = add_all.iter().next().unwrap();
            if add_all.len() == 1 {
            }
        }

        /*
        let mut add_alls = self.max_all.iter();
        let add_all = add_alls.next().unwrap();
        
        let mut count = match add_all.terms.get(&MulAll::one()) {
            None => {
                let nat_opt = if add_all.terms.is_empty() {
                    None
                } else {
                    Some(self.clone())
                };
                return (BigUint::zero(), nat_opt);
            },
            Some(count) => count,
        };
        for add_all in add_alls {
            match add_all.terms.get(&MulAll::one()) {
                None => return (BigUint::zero(), Some(self.clone())),
                Some(new_count) => count = cmp::max(count, new_count),
            }
        }
        */
    }
    */

    pub fn eliminates_var(&self, index: usize) -> bool {
        let Some(index) = self.usages.filter_index(index) else {
            return false;
        };
        self.max_all.eliminates_var(index)
    }
}

impl<S: Scheme> MaxAll<S> {
    pub fn zero() -> MaxAll<S> {
        MaxAll {
            terms: ordset! { AddAll::zero() },
        }
    }

    pub fn one() -> MaxAll<S> {
        MaxAll {
            terms: ordset! { AddAll::one() },
        }
    }

    pub fn succs(self, count: &NonZeroBigUint) -> MaxAll<S> {
        let terms = {
            self
            .terms
            .into_iter()
            .map(|add_all| add_all.succs(count))
            .collect()
        };
        MaxAll { terms }
    }

    pub fn max(lhs: MaxAll<S>, rhs: MaxAll<S>) -> MaxAll<S> {
        let mut terms = OrdSet::new();
        for add_all_0 in lhs.terms.into_iter() {
            if !{
                rhs
                .terms
                .iter()
                .any(|add_all_1| (&add_all_0 != add_all_1) && add_all_0.is_lte(add_all_1))
            } {
                terms.insert(add_all_0);
            }
        }
        let mut retained = Vec::new();
        for add_all_1 in rhs.terms.into_iter() {
            if !{
                terms
                .iter()
                .any(|add_all_0| add_all_1.is_lte(add_all_0))
            } {
                retained.push(add_all_1);
            }
        }
        terms.extend(retained);
        MaxAll { terms }
    }

    pub fn add(lhs: &MaxAll<S>, rhs: &MaxAll<S>) -> MaxAll<S> {
        let mut terms = ordset! { AddAll::zero() };
        for add_all_0 in lhs.terms.iter() {
            for add_all_1 in rhs.terms.iter() {
                let add_all = AddAll::add(add_all_0, add_all_1);
                if terms.iter().any(|prev_add_all| add_all.is_lte(prev_add_all)) {
                    continue;
                }
                terms = terms.into_iter().filter(|prev_add_all| !prev_add_all.is_lte(&add_all)).collect();
                terms.insert(add_all);
            }
        }
        MaxAll { terms }
    }

    pub fn mul(lhs: &MaxAll<S>, rhs: &MaxAll<S>) -> MaxAll<S> {
        let mut terms = ordset! { AddAll::zero() };
        for add_all_0 in lhs.terms.iter() {
            for add_all_1 in rhs.terms.iter() {
                let add_all = AddAll::mul(add_all_0, add_all_1);
                if terms.iter().any(|prev_add_all| add_all.is_lte(prev_add_all)) {
                    continue;
                }
                terms = terms.into_iter().filter(|prev_add_all| !prev_add_all.is_lte(&add_all)).collect();
                terms.insert(add_all);
            }
        }
        MaxAll { terms }
    }

    pub fn mul_non_zero_constant(self, n: &NonZeroBigUint) -> MaxAll<S> {
        let terms = {
            self
            .terms
            .into_iter()
            .map(|add_all| add_all.mul_non_zero_constant(n))
            .collect()
        };
        MaxAll { terms }
    }

    pub fn from_constant_non_zero(val: NonZeroBigUint) -> MaxAll<S> {
        MaxAll {
            terms: ordset! { AddAll::from_constant_non_zero(val) },
        }
    }

    pub fn from_stuck(val: RawStuck<S>) -> MaxAll<S> {
        MaxAll {
            terms: ordset! { AddAll::from_stuck(val) },
        }
    }

    pub fn is_zero(&self) -> bool {
        let mut iter = self.terms.iter();
        let add_all = iter.next().unwrap();
        match iter.next() {
            None => add_all.is_zero(),
            Some(_) => false,
        }
    }

    pub fn succs_count(&self) -> BigUint {
        let mut count_opt = None;
        for add_all in self.terms.iter() {
            match add_all.terms.get(&MulAll::one()) {
                None => return BigUint::zero(),
                Some(next_count) => match count_opt {
                    Some(count) => count_opt = Some(cmp::min(count, next_count)),
                    None => count_opt = Some(next_count),
                },
            }
        }
        count_opt.unwrap().clone().into_big_uint()
    }

    pub fn strict_sub_non_zero_constant(&self, val: &NonZeroBigUint) -> MaxAll<S> {
        let terms = {
            self
            .terms
            .iter()
            .map(|add_all| add_all.strict_sub_non_zero_constant(val))
            .collect()
        };
        MaxAll { terms }
    }

    /*
    pub fn try_decrement(&self) -> Option<MaxAll<S>> {
        let terms = {
            self
            .terms
            .iter()
            .map(|add_all| add_all.try_decrement())
            .collect::<Option<OrdSet<AddAll<S>>>>()?
        };
        Some(MaxAll { terms })
    }

    pub fn is_single_term(&self) -> bool {
        let mut iter = self.terms.iter();
        let add_all = iter.next().unwrap();
        match iter.next() {
            None => add_all.is_single_term(),
            Some(_) => false,
        }
    }

    pub fn into_single_term(self) -> RawStuck<S> {
        let mut iter = self.terms.into_iter();
        let add_all = iter.next().unwrap();
        debug_assert!(iter.next().is_none());
        add_all.into_single_term()
    }
    */

    pub fn iter_terms(&self) -> impl Iterator<Item = &RawStuck<S>> {
        self.terms.iter().flat_map(|add_all| add_all.iter_terms())
    }

    /*
    pub fn try_map_inner<F, E>(&self, target_len: usize, func: &mut F) -> Result<RawTm<S>, E>
    where
        F: FnMut(&RawStuck<S>) -> Result<RawTm<S>, E>,
    {
        let mut ret = RawTm::zero(target_len);
        for add_all in self.terms.iter() {
            ret = RawTm::max(ret, add_all.try_map_inner(target_len, func)?);
        }
        Ok(ret)
    }
    */

    pub fn unfilter(self, usages: &Usages) -> MaxAll<S> {
        let terms = {
            self
            .terms
            .into_iter()
            .map(|add_all| add_all.unfilter(usages))
            .collect()
        };
        MaxAll { terms }
    }

    /*
    pub fn greatest_root(&self) -> Option<NonZeroBigUint> {
        self
        .terms
        .reduce(|add_all_0, add_all_1| {
            [add_all_0.greatest_root(), add_all_1.greatest_root()]
            .into_iter()
            .reduce(NonZeroBigUint::gcd)
        })
    }

    pub fn exact_nth_root(&self, n: NonZeroBigUint) -> MaxAll<S> {
        let terms = {
            self
            .terms
            .iter()
            .map(|add_all| add_all.exact_nth_root(n))
            .collect()
        };
        MaxAll { terms }
    }

    pub fn greatest_divisor(&self) -> Option<NonZeroBigUint> {
        self
        .terms
        .iter()
        .filter_map(|add_all| add_all.greatest_divisor())
        .reduce(NonZeroBigUint::gcd)
    }

    pub fn exact_div(&self, divisor: &NonZeroBigUint) -> MaxAll<S> {
        let terms = {
            self
            .terms
            .iter()
            .map(|add_all| add_all.exact_div(divisor))
            .collect()
        };
        MaxAll { terms }
    }

    pub fn greatest_subtrahend(&self) -> AddAll<S> {
        self.terms.iter().reduce(AddAll::greatest_common_subtrahend).unwrap()
    }

    pub fn exact_sub(&self, subtrahend: &AddAll) -> MaxAll<S> {
        let terms = {
            self
            .terms
            .iter()
            .map(|add_all| add_all.exact_sub(subtrahend))
            .collect()
        };
        MaxAll { terms }
    }
    */

    pub fn subst(&self, filter: &Usages, var_term: &RawTm<S>) -> RawTm<S> {
        let mut iter = self.terms.iter();
        let add_all = iter.next().unwrap();
        let mut ret = add_all.subst(filter, var_term);
        for add_all in iter {
            let rhs = add_all.subst(filter, var_term);
            ret = RawTm::max(ret, rhs);
        }
        ret
    }

    /*
    pub(crate) fn map_scheme<V: Scheme>(
        &self,
        map_user_ty: &mut impl FnMut(&S::UserTy) -> V::UserTy,
        map_user_term: &mut impl FnMut(&S::UserTm) -> V::UserTm,
    ) -> MaxAll<V> {
        let terms = self.terms.iter().map(|add_all| add_all.map_scheme(map_user_ty, map_user_term)).collect();
        MaxAll { terms }
    }
    */

    pub fn eliminates_var(&self, index: usize) -> bool {
        self.terms.iter().any(|add_all| add_all.eliminates_var(index))
    }
}

impl<S: Scheme> AddAll<S> {
    pub fn zero() -> AddAll<S> {
        AddAll {
            terms: ordmap! {},
        }
    }

    pub fn one() -> AddAll<S> {
        AddAll {
            terms: ordmap! { MulAll::one() => NonZeroBigUint::one() },
        }
    }

    pub fn succs(mut self, count: &NonZeroBigUint) -> AddAll<S> {
        match self.terms.entry(MulAll::one()) {
            ordmap::Entry::Occupied(mut entry) => {
                *entry.get_mut() += count;
            },
            ordmap::Entry::Vacant(entry) => {
                entry.insert(count.clone());
            },
        }
        self
    }

    pub fn add(lhs: &AddAll<S>, rhs: &AddAll<S>) -> AddAll<S> {
        let mut terms = lhs.terms.clone();
        for (mul_all, multiplicity) in rhs.terms.iter() {
            match terms.entry(mul_all.clone()) {
                ordmap::Entry::Occupied(mut entry) => {
                    *entry.get_mut() += multiplicity;
                },
                ordmap::Entry::Vacant(entry) => {
                    entry.insert(multiplicity.clone());
                },
            }
        }
        AddAll { terms }
    }

    pub fn mul(lhs: &AddAll<S>, rhs: &AddAll<S>) -> AddAll<S> {
        let mut terms = ordmap! {};
        for (mul_all_0, multiplicity_0) in lhs.terms.iter() {
            for (mul_all_1, multiplicity_1) in rhs.terms.iter() {
                let mul_all = MulAll::mul(mul_all_0, mul_all_1);
                let multiplicity = multiplicity_0 * multiplicity_1;
                match terms.entry(mul_all) {
                    ordmap::Entry::Occupied(mut entry) => {
                        *entry.get_mut() += multiplicity;
                    },
                    ordmap::Entry::Vacant(entry) => {
                        entry.insert(multiplicity);
                    },
                }
            }
        }
        AddAll { terms }
    }

    pub fn mul_non_zero_constant(self, n: &NonZeroBigUint) -> AddAll<S> {
        let terms = {
            self
            .terms
            .into_iter()
            .map(|(mul_all, multiplicity)| {
                let multiplicity = multiplicity * n;
                (mul_all, multiplicity)
            })
            .collect()
        };
        AddAll { terms }
    }

    pub fn from_constant_non_zero(val: NonZeroBigUint) -> AddAll<S> {
        AddAll {
            terms: ordmap! { MulAll::one() => val },
        }
    }

    pub fn from_stuck(val: RawStuck<S>) -> AddAll<S> {
        AddAll {
            terms: ordmap! { MulAll::from_stuck(val) => NonZeroBigUint::one() },
        }
    }

    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    pub fn strict_sub_non_zero_constant(&self, val: &NonZeroBigUint) -> AddAll<S> {
        let (count, terms) = self.terms.extract(&MulAll::one()).unwrap();
        let count = count.strict_sub(val);
        let terms = match NonZeroBigUint::new(count) {
            None => terms,
            Some(count) => terms.update(MulAll::one(), count),
        };
        AddAll { terms }
    }

    /*
    pub fn try_decrement(&self) -> Option<AddAll<S>> {
        if !self.terms.contains_key(&MulAll::one()) {
            return None;
        }

        let mut terms = ordmap! {};
        for (mul_all, multiplicity) in self.terms.iter() {
            if mul_all.is_one() {
                if let Some(multiplicity) = multiplicity.try_decrement() {
                    terms.insert(mul_all.clone(), multiplicity);
                }
            } else {
                terms.insert(mul_all.clone(), multiplicity.clone());
            }
        }
        Some(AddAll { terms })
    }
    */

    pub fn is_single_term(&self) -> bool {
        let mut iter = self.terms.iter();
        match iter.next() {
            None => false,
            Some((mul_all, multiplicity)) => {
                iter.next().is_none() && multiplicity.is_one() && mul_all.is_single_term()
            },
        }
    }

    pub fn into_single_term(self) -> RawStuck<S> {
        let mut iter = self.terms.into_iter();
        let (mul_all, multiplicity) = iter.next().unwrap();
        debug_assert!(iter.next().is_none());
        debug_assert!(multiplicity.is_one());
        mul_all.into_single_term()
    }

    pub fn iter_terms(&self) -> impl Iterator<Item = &RawStuck<S>> {
        self.terms.iter().flat_map(|(mul_all, _multiplicity)| mul_all.iter_terms())
    }

    pub fn is_lte(&self, other: &AddAll<S>) -> bool {
        for (mul_all_0, multiplicity_0) in self.terms.iter() {
            match other.terms.get(mul_all_0) {
                None => return false,
                Some(multiplicity_1) => {
                    if multiplicity_0 > multiplicity_1 {
                        return false;
                    }
                },
            }
        }
        true
    }

    /*
    pub fn try_map_inner<F, E>(&self, target_len: usize, func: &mut F) -> Result<RawTm<S>, E>
    where
        F: FnMut(&RawStuck<S>) -> Result<RawTm<S>, E>,
    {
        let mut ret = RawTm::zero(target_len);
        for (mul_all, multiplicity) in self.terms.iter() {
            let rhs = {
                mul_all
                .try_map_inner(target_len, func)?
                .mul_constant_non_zero(multiplicity)
            };
            ret = RawTm::add(ret, rhs);
        }
        Ok(ret)
    }
    */

    pub fn unfilter(self, usages: &Usages) -> AddAll<S> {
        let terms = {
            self
            .terms
            .into_iter()
            .map(|(mul_all, multiplicity)| (mul_all.unfilter(usages), multiplicity))
            .collect()
        };
        AddAll { terms }
    }

    /*
    pub fn greatest_root(&self) -> Option<NonZeroBigUint> {
        let mut iter = self.terms.iter();
        let (mul_all, multiplicity) = iter.next()?;
        if iter.next().is_some() {
            return Some(NonZeroBigUint::one());
        }

        [mul_all.greatest_root(), multiplicity.greatest_root()]
        .into_iter()
        .reduce(NonZeroBigUint::gcd)
    }

    pub fn exact_nth_root(&self, n: NonZeroBigUint) -> AddAll<S> {
        let mut iter = self.terms.iter();
        let Some((mul_all, multiplicity)) = match iter.next() else {
            return self.clone();
        };
        if iter.next().is_some() {
            assert!(n.is_one());
            return self.clone();
        }
        let mul_all = mul_all.exact_nth_root(n);
        let multiplicity = multiplicity.exact_nth_root(n);
        AddAll {
            terms: [(mul_all, multiplicity)].into_iter().collect(),
        }
    }

    pub fn greatest_divisor(&self) -> Option<NonZeroBigUint> {
        self.terms.values().reduce(NonZeroBigUint::gcd)
    }

    pub fn exact_div(&self, divisor: &NonZeroBigUint) -> AddAll<S> {
        let terms = {
            self
            .terms
            .iter()
            .map(|(mul_all, multiplicity)| {
                let multiplicity = multiplicity.exact_div(divisor);
                (mul_all.clone(), multiplicity)
            })
            .collect()
        };
        AddAll { terms }
    }

    pub fn greatest_common_subtrahend(add_all_0: &AddAll<S>, add_all_1: &AddAll<S>) -> AddAll<S> {
        let terms = {
            add_all_0
            .terms
            .iter()
            .filter_map(|(mul_all, multiplicity_0)| {
                let multiplicity_1 = add_all_1.terms.get(mul_all)?;
                let multiplicity = cmp::min(multiplicity_0, multiplicity_1);
                Some((mul_all.clone(), multiplicity))
            })
            .collect()
        };
        AddAll { terms }
    }

    pub fn exact_sub(&self, subtrahend: &AddAll<S>) -> AddAll<S> {
        assert!(subtrahend.terms.keys().all(|mul_all| self.terms.contains_key(mul_all)));
        let terms = {
            self
            .terms
            .iter()
            .filter_map(|(mul_all, multiplicity_0)| {
                match subtrahend.terms.get(mul_all) {
                    None => Some((mul_all.clone(), multiplicity.clone())),
                    Some(multiplicity_1) => {
                        let multiplicity = multiplicity_0.as_big_uint().strict_sub(multiplicity_1.as_big_uint());
                        let multiplicity = NonZeroBigUint::new(multiplicity)?;
                        Some((mul_all.clone(), multiplicity))
                    },
                }
            })
            .collect()
        };
        AddAll { terms }
    }
    */

    pub fn subst(&self, filter: &Usages, var_term: &RawTm<S>) -> RawTm<S> {
        let mut ret = RawTm::zero(filter.len().strict_sub(1));
        for (mul_all, multiplicity) in self.terms.iter() {
            let rhs = mul_all.subst(filter, var_term);
            let rhs = rhs.mul_constant_non_zero(multiplicity);
            ret = RawTm::add(ret, rhs);
        }
        ret
    }

    /*
    pub(crate) fn map_scheme<V: Scheme>(
        &self,
        map_user_ty: &mut impl FnMut(&S::UserTy) -> V::UserTy,
        map_user_term: &mut impl FnMut(&S::UserTm) -> V::UserTm,
    ) -> AddAll<V> {
        let terms = {
            self
            .terms
            .iter()
            .map(|(mul_all, multiplicity)| {
                let mul_all = mul_all.map_scheme(map_user_ty, map_user_term);
                (mul_all, multiplicity.clone())
            })
            .collect()
        };
        AddAll { terms }
    }
    */

    pub fn eliminates_var(&self, index: usize) -> bool {
        self.terms.keys().any(|mul_all| mul_all.eliminates_var(index))
    }
}

impl<S: Scheme> MulAll<S> {
    pub fn mul(lhs: &MulAll<S>, rhs: &MulAll<S>) -> MulAll<S> {
        let mut terms = lhs.terms.clone();
        for (term, exponent) in rhs.terms.iter() {
            match terms.entry(term.clone()) {
                ordmap::Entry::Occupied(mut entry) => {
                    *entry.get_mut() += exponent;
                },
                ordmap::Entry::Vacant(entry) => {
                    entry.insert(exponent.clone());
                },
            }
        }
        MulAll { terms }
    }

    pub fn one() -> MulAll<S> {
        MulAll {
            terms: ordmap! {},
        }
    }

    /*
    pub fn is_one(&self) -> bool {
        self.terms.is_empty()
    }
    */

    pub fn from_stuck(val: RawStuck<S>) -> MulAll<S> {
        MulAll {
            terms: ordmap! { val => NonZeroBigUint::one() },
        }
    }

    pub fn is_single_term(&self) -> bool {
        let mut iter = self.terms.iter();
        match iter.next() {
            None => false,
            Some((_, exponent)) => iter.next().is_none() && exponent.is_one(),
        }
    }

    pub fn into_single_term(self) -> RawStuck<S> {
        let mut iter = self.terms.into_iter();
        let (val, exponent) = iter.next().unwrap();
        debug_assert!(iter.next().is_none());
        debug_assert!(exponent.is_one());
        val
    }

    pub fn iter_terms(&self) -> impl Iterator<Item = &RawStuck<S>> {
        self.terms.iter().map(|(term, _exponent)| term)
    }

    /*
    pub fn try_map_inner<F, E>(&self, target_len: usize, func: &mut F) -> Result<RawTm<S>, E>
    where
        F: FnMut(&RawStuck<S>) -> Result<RawTm<S>, E>,
    {
        let mut ret = RawTm::one(target_len);
        for (term, exponent) in self.terms.iter() {
            let rhs = func(term)?.pow_constant_non_zero(exponent);
            ret = RawTm::mul(ret, rhs);
        }
        Ok(ret)
    }
    */

    pub fn unfilter(self, usages: &Usages) -> MulAll<S> {
        let terms = {
            self
            .terms
            .into_iter()
            .map(|(stuck, exponent)| (stuck.unfilter(usages), exponent))
            .collect()
        };
        MulAll { terms }
    }

    /*
    pub fn greatest_root(&self) -> Option<NonZeroBigUint> {
        self.terms.values().reduce(NonZeroBigUint::gcd)
    }

    pub fn exact_nth_root(&self, n: NonZeroBigUint) -> MulAll<S> {
        let terms = {
            self
            .terms
            .iter()
            .map(|(term, exponent)| {
                let new_exponent = exponent.exact_div(n);
                (term, new_exponent)
            })
            .collect()
        };
        MulAll { terms }
    }
    */

    pub fn subst(&self, filter: &Usages, var_term: &RawTm<S>) -> RawTm<S> {
        let mut ret = RawTm::one(filter.len().strict_sub(1));
        for (stuck, exponent) in self.terms.iter() {
            let rhs = stuck.subst(filter, var_term);
            let rhs = rhs.pow_constant_non_zero(exponent);
            ret = RawTm::mul(ret, rhs);
        }
        ret
    }

    /*
    pub(crate) fn map_scheme<V: Scheme>(
        &self,
        map_user_ty: &mut impl FnMut(&S::UserTy) -> V::UserTy,
        map_user_term: &mut impl FnMut(&S::UserTm) -> V::UserTm,
    ) -> MulAll<V> {
        let terms = {
            self
            .terms
            .iter()
            .map(|(term, exponent)| {
                let term = term.map_scheme(map_user_ty, map_user_term);
                (term, exponent.clone())
            })
            .collect()
        };
        MulAll { terms }
    }
    */

    pub fn eliminates_var(&self, index: usize) -> bool {
        self.terms.keys().any(|term| term.eliminates_var(index))
    }
}

