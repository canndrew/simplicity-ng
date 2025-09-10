This is the working bits of the SimplicityNG compiler. The crates are:

* core-tt

  The core type-theory implementation. Implements Martin-Lof type theory
  (MLTT) with eta equality, uniqueness-of-identity-proofs and injective type
  constructors. Provides an API for constructing terms in MLTT and enforces
  that terms are well formed (eg. correctly typed and scoped).

* more-tt

  A plethora of utilities for core-tt. Seperate from core-tt so that it can
  rely purely on core-tt's high-level (correctness-enforcing) API.

* inference

  A type inference engine. Can be used to create core-tt terms with holes for
  terms/types to be inferred and then tries to infer them.

* debug

  Some miscellaneous debug utilities for when things break.

* small-bit-vec

  A bit vector that fits in the size of a `usize` and only heap-allocates
  when its length reaches `usize::BITS`.

* parser

  A parser. Not used by anything else here because the crates that depend on
  it are currently in shambles, not building and need to be ported to recent
  versions of the above crates. Should probably be replaced with a
  chumsky-based parser anyway.

