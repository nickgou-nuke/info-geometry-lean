# Cyclic triality and cyclotomic units

## Ground-truth contract

`CyclotomicTrialityOrderObstruction` distinguishes the order-two group
`(ZMod 3)ˣ` from `Multiplicative (ZMod 3)`, of order three. The correct
relationship of units to additive automorphisms is already provided by
Mathlib's `ZMod.AddAutEquivUnits`; no new identification of these groups is
asserted here.

`GaloisZornTrialityBridge.galoisActionOnTriality` is an existing pointwise
additive action on the full `ZornCore.Zorn` carrier, with additive composition
and determinant preservation. The completion packages that action as a
native group homomorphism into `Equiv.Perm ZornCore.Zorn`, proves faithfulness
using the existing `U e1` element, and proves multiplicativity by transporting
the existing `canonicalTriality_mul` through the injective
`CanonicalZornProjectiveTKKBridge.coreToCanonical` map. No associative ring
structure is imposed on the nonassociative Zorn multiplication.

This is a faithful cyclic coordinate action, not a Galois representation
obtained from the cyclotomic unit character, nor a classification of D4
triality or all Zorn automorphisms. Existing D4 and four-plane permutation
actions have other carriers and are not replacements for this carrier map.

## Verification

The shared-lock build of both this audit target and
`InfoGeometry.OperatorAlgebra.CanonicalZornCurrentTraceSplitAudit` passed
(9,385 jobs). This target reports seven axiom checks, including the existing
Mathlib equivalence; all use only `propext`, `Classical.choice`, and
`Quot.sound`. No warnings originate in the new modules. Independent semantic
review passed. Independent QA reran both targets successfully (9,385 jobs),
confirmed all eleven combined axiom reports, and found zero traps in strict
screening of the four new Lean files. Scoped diff checks passed. The rerun
reported 852 warning lines: zero from these sources, 849 from dependencies,
and three package/other warnings. Acceptance is limited to the contract above.
