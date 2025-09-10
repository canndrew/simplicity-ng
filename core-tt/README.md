# core-tt

This is the core type-theory implementation for SimplicityHL.

It implements a variant of [Martin-Löf type theory (MLTT)][1] with some additional
axioms for [eta-reduction][2], [uniqueness of identity proofs][3], and [injectivity of
type-formers][4].

It allows you to create and manipulate terms in this core theory
and enforces that they are always well-typed and well-scoped.

What this library is *not*:
* A parser.
* A type-checker.
* A type-inference engine.
* A code-generation backend.

Rather, its a library designed to be used by these other parts of a full
compiler implementation.


[1]: https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory
[2]: https://ncatlab.org/nlab/show/eta-conversion
[3]: https://en.wikipedia.org/wiki/Uniqueness_of_identity_proofs
[4]: 
