use crate::priv_prelude::*;

#[derive_where(Debug, Clone, Eq, Hash)]
pub struct RawCtx<S: Scheme> {
    pub(crate) cons_opt: Option<Arc<RawCtxCons<S>>>,
}

impl<S: Scheme> PartialEq for RawCtx<S> {
    fn eq(&self, other: &RawCtx<S>) -> bool {
        match (&self.cons_opt, &other.cons_opt) {
            (None, None) => true,
            (Some(cons_0), Some(cons_1)) => Arc::ptr_eq(cons_0, cons_1),
            _ => false,
        }
    }
}

#[derive_where(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RawCtxCons<S: Scheme> {
    pub(crate) parent: RawCtx<S>,
    pub(crate) var_ty: RawTy<S>,
}

impl<S: Scheme> RawCtx<S> {
    pub(crate) fn len(&self) -> usize {
        match &self.cons_opt {
            None => 0,
            Some(cons) => 1 + cons.var_ty.usages.len(),
        }
    }

    pub(crate) fn root() -> RawCtx<S> {
        RawCtx {
            cons_opt: None,
        }
    }

    pub(crate) fn nth_parent(&self, n: usize) -> &RawCtx<S> {
        let mut ret = self;
        for _ in 0..n {
            let cons = ret.cons_opt.as_ref().unwrap();
            ret = &cons.parent;
        }
        ret
    }

    pub(crate) fn cons(&self, var_ty: RawTy<S>) -> RawCtx<S> {
        RawCtx {
            cons_opt: Some(Arc::new(RawCtxCons {
                parent: self.clone(),
                var_ty,
            })),
        }
    }

    /*
    pub(crate) fn get_ty_and_de_brujin(&self, name: &S) -> Option<(&RawTy<S>, usize)> {
        let mut de_brujin = 0;
        let mut raw_ctx = self;
        loop {
            let cons = raw_ctx.cons_opt.as_ref()?;
            if let Some(var_name) = &cons.var_name_opt && var_name == name {
                return Some((&cons.var_ty, de_brujin));
            }
            de_brujin += 1;
            raw_ctx = &cons.parent;
        }
    }
    */

    pub fn get_raw_ty(&self, ctx_len: usize, index: usize) -> &RawTy<S> {
        let de_brujin = ctx_len.strict_sub(index + 1);
        let raw_ctx = self.nth_parent(de_brujin);
        &raw_ctx.cons_opt.as_ref().unwrap().var_ty
    }

    pub fn filter(&self, ctx_len: usize, usages: &Usages) -> RawCtx<S> {
        if usages.is_ones() {
            return self.clone();
        }
        let cons = self.cons_opt.as_ref().unwrap();
        let ctx_len = ctx_len.strict_sub(1);
        let raw_ctx = cons.parent.filter(ctx_len, usages);
        if usages[ctx_len] {
            let var_ty_usages = cons.var_ty.usages.clone_filter_prefix(ctx_len, usages);
            let var_ty = Weaken {
                usages: var_ty_usages,
                weak: cons.var_ty.weak.clone(),
            };
            raw_ctx.cons(var_ty)
        } else {
            raw_ctx
        }
    }

    pub fn to_sigma(&self, ty: RawTy<S>) -> RawTy<S> {
        match self.cons_opt.as_ref() {
            None => ty,
            Some(cons) => {
                let RawCtxCons { parent, var_ty } = &**cons;
                let tail_ty = RawScope::new(var_ty.clone(), ty);
                let ty = RawTy::sigma(tail_ty);
                parent.to_sigma(ty)
            },
        }
    }

    pub fn to_sigma_scope<T>(&self, scope: RawScope<S, T>) -> RawScope<S, T>
    where
        T: Substitute<S, RawSubstOutput = T>,
        T: Clone + PartialEq,
    {
        match self.cons_opt.as_ref() {
            None => scope,
            Some(cons) => {
                let RawCtxCons { parent, var_ty } = &**cons;
                let ctx_len = var_ty.usages.len();
                let mut tail_ty = RawScope::new(var_ty.clone(), scope.unfilter_out(|scope| scope.var_ty.clone()));
                let sigma_ty = RawTy::sigma(tail_ty.clone());

                let mut scope = RawScope::new(var_ty.clone(), scope);
                scope.weaken(1);
                tail_ty.weaken(1);
                let var_term = RawTm::var(ctx_len + 1, ctx_len, &sigma_ty);
                let inner = {
                    scope
                    .bind(&RawTm::proj_head(tail_ty.clone(), var_term.clone()))
                    .bind(&RawTm::proj_tail(tail_ty.clone(), var_term.clone()))
                };
                let scope = RawScope::new(sigma_ty, inner);
                parent.to_sigma_scope(scope)
            },
        }
    }

    pub fn fill_transitive_usages(&self, usages: &mut Usages) {
        match self.cons_opt.as_ref() {
            None => (),
            Some(cons) => {
                let RawCtxCons { parent, var_ty } = &**cons;
                if usages[var_ty.usages.len()] {
                    usages.or_assign_prefix(&var_ty.usages);
                }
                parent.fill_transitive_usages(usages);
            },
        }
    }

    /*
    pub fn map_scheme<V: Scheme>(
        &self,
        map_user_ty: &mut impl FnMut(&S::UserTy) -> V::UserTy,
        map_user_term: &mut impl FnMut(&S::UserTm) -> V::UserTm,
    ) -> RawCtx<V> {
        RawCtx {
            cons_opt: self.cons_opt.as_ref().map(|cons| Arc::new(cons.map_scheme(map_user_ty, map_user_term))),
        }
    }
    */
}

impl<S: Scheme> RawCtxCons<S> {
    /*
    pub fn map_scheme<V: Scheme>(
        &self,
        map_user_ty: &mut impl FnMut(&S::UserTy) -> V::UserTy,
        map_user_term: &mut impl FnMut(&S::UserTm) -> V::UserTm,
    ) -> RawCtxCons<V> {
        let RawCtxCons { parent, var_ty } = self;
        let parent = parent.map_scheme(map_user_ty, map_user_term);
        let var_ty = var_ty.map_scheme(map_user_ty, map_user_term);
        RawCtxCons { parent, var_ty }
    }
    */
}

