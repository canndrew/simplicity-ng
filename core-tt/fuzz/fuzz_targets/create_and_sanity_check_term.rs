#![recursion_limit = "300"]
#![no_main]

use {
    core_tt::{Tm, Interner, TyKind},
    arbitrary::Arbitrary,
    lazy_static::lazy_static,
    libfuzzer_sys::{
        arbitrary::Unstructured,
        fuzz_target,
    },
};

struct Scheme;
impl core_tt::Scheme for Scheme {
    type Tag = ();

    fn interner() -> &'static Interner<Scheme> {
        lazy_static! {
            static ref INTERNER: Interner<Scheme> = Interner::new();
        }
        &*INTERNER
    }
}

fuzz_target!(|data: &[u8]| {
    fn inner(u: &mut Unstructured<'_>) -> arbitrary::Result<()> {
        let term: Tm<Scheme> = Tm::arbitrary(u)?;
        term.sanity_check();
        if term.ctx().len() == 0 {
            assert!(!matches!(term.ty().kind(), TyKind::Never));
        }
        Ok(())
    }

    let mut u = Unstructured::new(data);
    let _ = inner(&mut u);
});

