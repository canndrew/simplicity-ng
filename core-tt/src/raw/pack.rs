use crate::priv_prelude::*;

pub trait RawContextualTuple<S: Scheme, const ARITY: usize> {
    /*
    type RawTupleMappedScheme<V: Scheme>:
            RawContextualTuple<V, ARITY>
            + Clone + PartialEq;
    */

    fn filter_self(self) -> (Usages, Self);
    fn unfilter(self, usages: &Usages) -> Self;
    /*
    fn tuple_map_scheme<V: Scheme>(
        &self,
        map_user_ty: &mut impl FnMut(&S::UserTy) -> V::UserTy,
        map_user_term: &mut impl FnMut(&S::UserTm) -> V::UserTm,
    ) -> Self::RawTupleMappedScheme<V>;
    */
}

pub trait SubstituteTuple<S: Scheme, const ARITY: usize> {
    type RawTupleSubstOutput:
            RawContextualTuple<S, ARITY>
            + SubstituteTuple<S, ARITY, RawTupleSubstOutput = Self::RawTupleSubstOutput>
            + Clone + PartialEq;

    fn to_tuple_subst_output(&self) -> Self::RawTupleSubstOutput;
    fn tuple_subst(&self, filter: &Usages, var_term: &RawTm<S>) -> Self::RawTupleSubstOutput;
}

macro_rules! impl_tuple_traits {
    ($($ty:ident,)*) => {
        impl<S: Scheme, $($ty,)*> RawContextualTuple<S, {count_tokens!($($ty)*)}> for ($($ty,)*)
        where
            $($ty: RawContextual<S>,)*
        {
            //type RawTupleMappedScheme<V: Scheme> = ($($ty::RawMappedScheme<V>,)*);

            #[allow(non_snake_case)]
            fn filter_self(self) -> (Usages, Self) {
                let ($(mut $ty,)*) = self;
                let usages = Usages::merge_mut([$($ty.usages_mut(),)*]);
                (usages, ($($ty,)*))
            }

            #[allow(non_snake_case)]
            #[allow(unused)]
            fn unfilter(self, usages: &Usages) -> Self {
                let ($($ty,)*) = self;
                ($($ty.unfilter(usages),)*)
            }

            /*
            #[allow(non_snake_case)]
            #[allow(unused)]
            fn tuple_map_scheme<V: Scheme>(
                &self,
                map_user_ty: &mut impl FnMut(&S::UserTy) -> V::UserTy,
                map_user_term: &mut impl FnMut(&S::UserTm) -> V::UserTm,
            ) -> ($($ty::RawMappedScheme<V>,)*) {
                let ($($ty,)*) = self;
                ($($ty.map_scheme(map_user_ty, map_user_term),)*)
            }
            */
        }

        impl<S: Scheme, $($ty,)*> SubstituteTuple<S, {count_tokens!($($ty)*)}> for ($($ty,)*)
        where
            $($ty: Substitute<S>,)*
        {
            type RawTupleSubstOutput = ($($ty::RawSubstOutput,)*);

            #[allow(non_snake_case)]
            fn to_tuple_subst_output(&self) -> ($($ty::RawSubstOutput,)*) {
                let ($($ty,)*) = self;
                ($($ty.to_subst_output(),)*)
            }

            #[allow(non_snake_case)]
            #[allow(unused)]
            fn tuple_subst(&self, filter: &Usages, var_term: &RawTm<S>) -> ($($ty::RawSubstOutput,)*) {
                let ($($ty,)*) = self;
                ($($ty.subst(filter, var_term),)*)
            }
        }
    };
}

impl_tuple_traits!();
impl_tuple_traits!(T0,);
impl_tuple_traits!(T0,T1,);
impl_tuple_traits!(T0,T1,T2,);
impl_tuple_traits!(T0,T1,T2,T3,);
impl_tuple_traits!(T0,T1,T2,T3,T4,);
impl_tuple_traits!(T0,T1,T2,T3,T4,T5,);
impl_tuple_traits!(T0,T1,T2,T3,T4,T5,T6,);
impl_tuple_traits!(T0,T1,T2,T3,T4,T5,T6,T7,);

#[derive(Clone, Debug, PartialEq)]
pub struct RawPack<S: Scheme, const ARITY: usize, T: RawContextualTuple<S, ARITY>> {
    _name: PhantomData<S>,
    usages: Usages,
    tuple: T,
}

impl<S, const ARITY: usize, T> RawPack<S, ARITY, T>
where
    S: Scheme,
    T: RawContextualTuple<S, ARITY> + Clone + PartialEq,
{
    pub fn from_tuple(tuple: T) -> RawPack<S, ARITY, T> {
        let (usages, tuple) = tuple.filter_self();
        RawPack {
            _name: PhantomData,
            usages,
            tuple,
        }
    }

    pub fn to_tuple(&self) -> T {
        self.tuple.clone().unfilter(&self.usages)
    }

    pub fn into_tuple(self) -> T {
        self.tuple.unfilter(&self.usages)
    }
}

impl<S, const ARITY: usize, T> RawContextual<S> for RawPack<S, ARITY, T>
where
    S: Scheme,
    T: RawContextualTuple<S, ARITY> + Clone + PartialEq,
{
    //type RawMappedScheme<V: Scheme> = RawPack<V, ARITY, T::RawTupleMappedScheme<V>>;

    fn usages_mut(&mut self) -> &mut Usages {
        &mut self.usages
    }

    fn usages(&self) -> &Usages {
        &self.usages
    }

    fn usages_len(&self) -> usize {
        self.usages.len()
    }

    fn clone_filter(&self, usages: &Usages) -> RawPack<S, ARITY, T> {
        RawPack {
            _name: PhantomData,
            usages: self.usages.clone_filter(usages),
            tuple: self.tuple.clone(),
        }
    }

    fn clone_unfilter(&self, usages: &Usages) -> RawPack<S, ARITY, T> {
        RawPack {
            _name: PhantomData,
            usages: self.usages.clone_unfilter(usages),
            tuple: self.tuple.clone(),
        }
    }

    fn unfilter(mut self, usages: &Usages) -> RawPack<S, ARITY, T> {
        self.usages.unfilter(usages);
        self
    }

    fn filter_self(mut self) -> (Usages, RawPack<S, ARITY, T>) {
        let num_usages = self.usages.count_ones();
        let usages = mem::replace(&mut self.usages, Usages::ones(num_usages));
        (usages, self)
    }

    fn weaken(&mut self, ext_len: usize) {
        self.usages.weaken(ext_len);
    }

    fn clone_weaken(&self, ext_len: usize) -> RawPack<S, ARITY, T> {
        let usages = self.usages.clone_weaken(ext_len);
        let tuple = self.tuple.clone();
        RawPack { _name: PhantomData, usages, tuple }
    }

    /*
    fn map_scheme<V: Scheme>(
        &self,
        map_user_ty: &mut impl FnMut(&S::UserTy) -> V::UserTy,
        map_user_term: &mut impl FnMut(&S::UserTm) -> V::UserTm,
    ) -> RawPack<V, ARITY, T::RawTupleMappedScheme<V>> {
        let usages = self.usages.clone();
        let tuple = self.tuple.tuple_map_scheme(map_user_ty, map_user_term);
        RawPack { _name: PhantomData, usages, tuple }
    }
    */
}

impl<S, const ARITY: usize, T> Substitute<S> for RawPack<S, ARITY, T>
where
    S: Scheme,
    T: RawContextualTuple<S, ARITY>,
    T: SubstituteTuple<S, ARITY>,
    T: Clone + PartialEq,
{
    type RawSubstOutput = RawPack<S, ARITY, T::RawTupleSubstOutput>;

    fn to_subst_output(&self) -> RawPack<S, ARITY, T::RawTupleSubstOutput> {
        let tuple = self.to_tuple();
        let tuple = tuple.to_tuple_subst_output();
        RawPack::from_tuple(tuple)
    }

    fn subst(&self, filter: &Usages, var_term: &RawTm<S>) -> RawPack<S, ARITY, T::RawTupleSubstOutput> {
        match self.usages.subst(filter, var_term) {
            ControlFlow::Break(usages) => {
                RawPack {
                    usages,
                    tuple: self.tuple.to_tuple_subst_output(),
                    _name: PhantomData,
                }
            },
            ControlFlow::Continue((unfilter, sub_filter, var_term)) => {
                let tuple = self.tuple.tuple_subst(&sub_filter, &var_term);
                let mut ret = RawPack::from_tuple(tuple);
                ret.usages.unfilter(&unfilter);
                ret
            },
        }
    }
}

