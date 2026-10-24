# Normalized Dirac self-adjointness: theorem contract

The existing counterexample `Canonical.PeirceSquareZeroExamples.reciprocal_sum_not_selfAdjoint`
uses the actual real matrix pair `2 E01` and `(1/2) E10`. Its square is a
star projection, but the sum is not self-adjoint.

Replacement on any `[Ring R] [StarRing R]`: for the existing
`IsMoorePenroseInverse a m` and `a*a=0`, prove
`IsSelfAdjoint (normalizedDirac a m) ↔ m = star a`.
Reuse `Core.DiracPeirceSuperalgebra.exactSupport_mul_normalizedDirac`
and `normalizedDirac_mul_exactSupport`: writing `p=a*m`, `Q=a+m`, these
are `p*Q=a` and `Q*p=m`. Since `p` is self-adjoint, taking adjoints proves
necessity; sufficiency is the ordinary self-adjointness of `a+star a`.

No positivity, C-star norm, characteristic restriction, or continuum claim.
The actual existing normalizedDirac and MP predicate remain the carriers.
The source search and independent semantic review found no identical iff in
the inspected Dirac/MP owners.

## Verification accepted with limited scope

Parent combined audit session 32686 passed (3,198 jobs, exit 0).
Independent kernel QA session 25438 also passed (3,198 jobs, exit 0),
recorded in `/tmp/mp-gns-final-qa.log`. Across the two batches, all eleven
axiom reports, six examples, and both noncommuting witnesses passed.
The self-adjointness iff uses `propext, Quot.sound`; the metric-equality iff
uses no axioms; the other nine reports use only the standard three axioms.
There were zero own-module warnings, 33 dependency warnings, and two package
notices. Semantic review passed, strict screening found zero traps, and
scoped diffs were clean. This acceptance covers the stated finite/algebraic
contracts only.
