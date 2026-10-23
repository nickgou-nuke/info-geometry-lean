# Split-octonion operator realignment

## Ground-truth contract

`Lie/SplitOctonionNonmultiplicativity.lean` supplies an explicit nonzero
associator and failure of multiplicativity for `imaginaryLeftMul`.
Its actual witnesses are `ex_X`, `ex_Y`, `ex_Z` from
`SplitOctonionImaginaryAction`, defined by imaginary coordinates. They are not
the idempotent basis elements described in the old example comment.

The existing positive alternative is already native Mathlib:
`SplitOctonionImaginaryAction.splitOctonionLeftCliffordRepresentation` is an
algebra homomorphism from `CliffordAlgebra leftCliffordQuadratic` to
`Module.End ℝ CanonicalZorn`. Its generator formula, square law and
anticommutator are proved in that owner. These preserve the quadratic relation,
not the split-octonion product. Associator criteria for full left multiplication
also exist, including `SplitOctonionLeftMultiplicationBridge.leftMulCompDefect_eq_zero_iff`.
They need no duplicate implementation here.

The additional statements use the exact existing `Imaginary` submodule and
`imaginaryLeftMul` linear map: evaluation at the unit recovers the input vector,
so this linear map is injective; alternativity and
`mem_null_iff_square_zero` identify square-zero operators precisely with
`NormLevel 0`. This distinguishes faithful vector encoding from the false
claim of octonion multiplication preservation. It also identifies the actual
nilpotent operator locus without replacing the noncommutative endomorphism carrier.

Search covered repo Lean occurrences of imaginaryLeftMul, its Clifford lift,
associator defects and existing multiplicativity criteria. Discovery receipt:
`/tmp/zorn-operator-realignment-discovery.json` (navigation only).

No faithfulness of the full Clifford algebra representation, classification of
its kernel, or associative octonion embedding is claimed.

## Verification

The locked build of `InfoGeometry.Lie.SplitOctonionOperatorRealignmentAudit`
completed successfully (4334 jobs). Its six axiom reports contain only standard
foundational axioms. Strict OpenGauss screening passed for the three touched
Lean files with zero traps. No touched-source warnings occurred; the build
replayed 420 dependency/package warning lines. Build log:
`/tmp/zorn-operator-audit.log`.

Independent A-A Poincare passed the final changes, including the corrected
namespace in this contract. Independent QA-A Popper returned
`ACCEPTED_WITH_LIMITED_SCOPE` after rerunning the locked build (4334 jobs),
six axiom reports, strict screening and diff checks. Independent build log:
`/tmp/zorn-operator-qa.log`.
No repository-wide verification or completion is claimed.
