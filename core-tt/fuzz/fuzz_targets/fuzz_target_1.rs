#![recursion_limit = "300"]
#![no_main]

use {
    core_tt::{
        Ctx, Interner,
        arbitrary::{arbitrary_ctx, arbitrary_ty_under_ctx, arbitrary_term_of_ty},
    },
    lazy_static::lazy_static,
    libfuzzer_sys::{
        arbitrary::Unstructured,
        fuzz_target,
    },
};

struct Scheme;
impl core_tt::Scheme for Scheme {
    type UserTy = ();
    type UserTm = ();

    fn user_ty_of((): &()) {}

    fn interner() -> &'static Interner<Scheme> {
        lazy_static! {
            static ref INTERNER: Interner<Scheme> = Interner::new();
        }
        &*INTERNER
    }
}

fuzz_target!(|data: &[u8]| {
    fn inner(u: &mut Unstructured<'_>) -> arbitrary::Result<()> {
        let ctx: Ctx<Scheme> = arbitrary_ctx(u)?;
        let head_ty = arbitrary_ty_under_ctx(&ctx, u)?;
        let tail_ty = head_ty.try_scope(|head_term| {
            arbitrary_ty_under_ctx(&head_term.ctx(), u)
        })?;
        let pair_ty = head_ty.sigma(tail_ty.unbind());
        let pair_term = arbitrary_term_of_ty(&pair_ty, u)?;

        let head_term = pair_term.proj_head();
        let tail_term = pair_term.proj_tail();
        let new_pair_term = head_term.pair(tail_ty.unbind(), &tail_term);
        /*
        let new_pair_term = {
            pair_term
            .split(
                |pair_term| pair_term.ty(),
                |head_term, tail_term| head_term.pair(&(), tail_ty.unbind(), &tail_term),
            )
        };
        */
        assert_eq!(pair_term, new_pair_term, "not equal!\n{:#?}\n{:#?}", pair_term, new_pair_term);

        Ok(())
    }

    let mut u = Unstructured::new(data);
    let _ = inner(&mut u);
});

