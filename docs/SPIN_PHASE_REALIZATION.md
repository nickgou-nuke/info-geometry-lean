# Constructive fixed-Cartan spin phases

## Ground-truth contract

`Physics/SpinAffineCasimirRigidity.lean` defines `mixedPlus`, `mixedMinus`
on the existing nuclear Wigner `SpinMatrix` carrier, with conjugated
coefficients in `mixedMinus`. Its `hyperbolic_counterexample` preserves the
ladder bracket but violates the fixed-Cartan bracket.
The positive classification `fixed_cartan_spin_relations_iff` already proves
that both relations hold exactly when `v = 0` and `Complex.normSq u = 1`.

The new construction realizes every permitted phase on the same carrier:
`phaseMatrix u = diag(u, 1)`. It is a member of Mathlib's unitary submonoid
when `normSq u = 1`. Conjugation by it fixes `isospin3`, sends `isospinPlus`
to `mixedPlus u 0`, and sends `isospinMinus` to `mixedMinus u 0`.
These equations use the original Pauli/ladder matrices without replacing them
or changing multiplication conventions. No assertion that this matrix has
determinant one is made. The existing classification and the explicit
construction together give the constructive alternative to hyperbolic mixing.

The exact phase/ladder conjugation API was not found in the searched spin
owner and its direct reflection/time-reversal consumers. The new focused
module is consumed by the existing spin audit.

## Verification

The locked `InfoGeometry.Canonical.SpinAffineExteriorAudit` build passed
(9,017 jobs). The phase definition and four theorems report only `propext`,
`Classical.choice`, and `Quot.sound`. Strict OpenGauss screening of owner and
audit reported zero traps; semantic-vacuity screening of the owner reported
zero findings. The new owner and modified audit have no warnings.

Independent A-A Pascal passed the final source review, closing the audit
integration finding. Independent QA Erdos reran the locked build and gates
against unchanged source hashes and passed this three-file patch. Its build
replayed cached compilation/axiom output; dependency sources replayed 469
warnings and two dirty-package warnings. This is limited patch verification,
not warning-free or repository-wide acceptance. The broader counterexample
replacement objective remains incomplete.
