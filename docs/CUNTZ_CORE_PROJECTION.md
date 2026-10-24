# Corrected quotient core projection

The existing `CuntzComplexStarBinaryGaugeDegreeZero` extracts degree zero
from the integer grading of the actual `ComplexStarCuntzAlg Bool` quotient.
The existing `CuntzComplexStarBinaryWordPairSpanBridge` proves that arbitrary
word pairs span that quotient. Combining these owners gives a constructive
replacement for an unsupported assertion that a diagonal coefficient readout
already defines a state on the full algebra.

`CuntzComplexStarBinaryCoreProjection.core` is the complex linear span of
word pairs with equal lengths. `projection` is the existing integer-grading
map followed by degree-zero extraction, packaged as a native `LinearMap`.
Span induction proves that it takes every quotient element into the core,
fixes every element of the core, and consequently has exactly that range.
It is idempotent, unital, and star-preserving, including conjugation of complex
coefficients. It is not asserted to be multiplicative or positive.

Source discovery also inspected `CantorBernoulliComplexStarFiniteStageBridge`
and its representation and matrix-unit theorems. Those maps identify finite
matrix observables after representation; equality in the quotient must not
be inferred from unproved faithfulness of the entire representation. The
next map obligation is a coherent injective star-algebra embedding of the
native matrix colimit into this quotient, with range this core. Positivity
of extraction and a KMS identity are still separate obligations.

Parent locked audit passed: session 78904, exit 0, 9395 jobs,
`/tmp/cuntz-core-projection-audit.log`. All seven theorems report only
`propext`, `Classical.choice`, and `Quot.sound`; zero own-source warnings.
Independent semantic review passed; strict screening found zero traps.
Distinct QA passed: session 7927, exit 0, 9395 jobs,
`/tmp/cuntz-core-projection-qa.log`. All seven axiom reports have the same
standard axiom set, with zero own-source warnings and zero strict-screen
traps. Scoped staged/worktree checks and forbidden-proof-source checks passed.
Dependency warnings remain; this is scoped acceptance, not repository-wide
completion.
