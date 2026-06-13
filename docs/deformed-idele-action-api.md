# Deformed Idele Action API

Lean owner: `lean/InfoGeometry/Canonical/DeformedIdeleAction.lean`

Generic algebra owner: `lean/InfoGeometry/Algebra/NonCommutativeIsometry.lean`

SymPy witness: `tools/sympy/deformed_idele_action.py`

This module formalizes the finite Cuntz readout behind the phrase "deformed
idelic action". The generic partial-isometry/noncommutativity lemmas live in
`InfoGeometry.Algebra.NonCommutativity`.

## Verified Readouts

| Theorem | Content |
|---|---|
| `InfoGeometry.Algebra.NonCommutativity.branch_commutator_eq_range_sub_source` | `S*S - S*S` read as `rangeProjection S - sourceProjection S` |
| `InfoGeometry.Algebra.NonCommutativity.isometry_branch_commutator_eq_range_sub_one` | if `S* S = 1`, then the branch commutator is `rangeProjection S - 1` |
| `InfoGeometry.Algebra.NonCommutativity.isometry_branch_commutator_ne_zero` | if `S* S = 1` and `rangeProjection S ≠ 1`, then the commutator is nonzero |
| `InfoGeometry.Algebra.NonCommutativity.rangeProjection_idempotent_of_partial_isometry` | a partial-isometry premise makes `S S*` idempotent |
| `InfoGeometry.Algebra.NonCommutativity.sourceProjection_idempotent_of_partial_isometry` | a partial-isometry premise makes `S* S` idempotent |
| `InfoGeometry.Algebra.NonCommutativity.two_sided_inverse_branch_commutator_zero` | a two-sided inverse collapses the commutator |
| `left_cuntz_branch_commutator` | Cuntz left branch specialization |
| `right_cuntz_branch_commutator` | Cuntz right branch specialization |
| `left_cuntz_branch_commutator_ne_zero` | Cuntz left branch is noncommutative under an explicit range mismatch |
| `right_cuntz_branch_commutator_ne_zero` | Cuntz right branch is noncommutative under an explicit range mismatch |
| `left_cuntz_rangeProjection_ne_one_of_right_ne_zero` | nonzero right branch forces left range projection to be proper |
| `right_cuntz_rangeProjection_ne_one_of_left_ne_zero` | nonzero left branch forces right range projection to be proper |
| `left_cuntz_branch_commutator_ne_zero_of_right_ne_zero` | nonzero right branch forces left branch noncommutativity |
| `right_cuntz_branch_commutator_ne_zero_of_left_ne_zero` | nonzero left branch forces right branch noncommutativity |
| `left_cuntz_branch_commutator_ne_zero'` | nontrivial-ring Cuntz left branch noncommutativity |
| `right_cuntz_branch_commutator_ne_zero'` | nontrivial-ring Cuntz right branch noncommutativity |
| `cuntz_branch_partition` | Cuntz range projections sum to `1` |

## Non-Claims

This API does not prove an adele or idele group theorem, quantum torus
construction, q-parameter dynamics, KMS/BEC transition, root-of-unity braid
representation, Galois action, C*-completion, zeta theorem, or RH consequence.

Those interpretations require separate proof-carrying analytic, topological,
or representation-theoretic context.
