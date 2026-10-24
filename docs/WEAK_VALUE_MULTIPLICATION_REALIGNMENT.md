# Weak-value multiplication contract

The existing `WeakPropertySeparation.weakValue_not_multiplicative` gives a
native finite-endomorphism example with weak square value zero and squared
weak value four. Preserve this example. Reuse `RegularBoundaryPair`,
`weakValue`, and `TwoBoundaryDyadCompression.boundaryDyad` without changing
carriers or replacing the functional with a probability state.

Prove the exact defect
`w(AB) - w(A)w(B) = w(A(1-P)B)` and characterize multiplicativity for all left
factors by `B pre = w(B) • pre`. The converse uses actual coordinate rank-one
endomorphisms to separate the residual vector. A line-preserving restriction
should carry the native algebra-hom structure; multiplicativity is proved,
not assumed. Existing same-ray/Hermitian dyad results are reused, not duplicated.

Source search covered maintained references to weakValue, boundaryDyad and
normalizedDyad, and direct reads of the functional, generic dyad, boundary
compression and counterexample owners. The proposed defect and characterization
were not found in that scoped search. Nonmultiplicativity alone does not imply
nonpositivity; do not promote the old explanatory comment to a theorem.
Implemented in `Streaming.WeakValueMultiplication` and
`Streaming.WeakValueLineAlgebra`: six multiplication/separation lemmas, the
native line-stabilizer subalgebra, its exact membership criteria, and a native
`AlgHom` to ℂ. The subalgebra contains singular operators, including the boundary
dyad; it is not restricted to invertible stabilizers. No positivity claim is made.

The original negative theorem is unchanged. Its misleading positivity comment
is corrected. The new audit computes its complementary-dyad defect as `-4`,
checks boundary-dyad membership, and checks character normalization.

Independent semantic review passed. Final QA session 53912 terminated with
exit zero (8944 jobs), all eleven declaration reports exactly
`propext`, `Classical.choice`, `Quot.sound`, zero new-module warnings,
zero strict-screen traps, clean scoped diffs, and three compiled examples.
Log: `/tmp/weak-mul-qa.log` (session-local evidence). Existing dependencies and
the docstring-only owner retain unrelated warnings. Accepted with this scope;
not a repository-wide certification.
