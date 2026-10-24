# Zorn color bilinears — G-A contract

Uncompiled sandbox proposal; no live edits or builds. Parent owns promotion,
Popper AA and Ampere serial QA. This file depends on expected promoted APIs.

## Dependencies read

- `scratch/ZornSignedCAR20261024v2.lean`, expected owner
  `InfoGeometry.Algebra.ZornSignedCAR`: `L_U_U_anticommutator`,
  `L_negV_negV_anticommutator`, `L_U_negV_anticommutator`, all in
  `InfoGeometry.Algebra.ZornVectorMatrix`. The mixed contraction is a scalar
  multiple of the endomorphism identity; simplification turns it into the
  generic owner's conditional negative identity.
- Live `Algebra/ZornLeftGrading`: `left_E11_tangent_offDiagonal` and
  `left_diagonal_difference_eq_two_projector_sub_one`.
- Live `OperatorAlgebra/QuadraticNoncommutativeIdentity` owns negative-CAR
  bilinear closure. The expected appended action APIs are
  `negative_car_bilinear_action_forward` and
  `negative_car_bilinear_action_backward`, from
  `scratch/NegativeCARActions20261024.lean`; they were not yet in the live
  owner when initially read for this task. No scratch module is imported.

## Exact additions

Namespace `InfoGeometry.Algebra.ZornColorBilinears`, arbitrary `CommRing R`.
`E i j := -(L_map (U i) * L_map (-V j))` has type
`Module.End R (ZornVectorMatrix R)`, using the actual existing carrier.

- `E_action_U`: `[Eij,L_Uk] = δjk L_Ui`.
- `E_action_negV`: `[Eij,L_-Vk] = -δik L_-Vj`.
- `E_commutator`: `[Eij,Elm] = δjl Eim - δmi Elj`.
- `left_E11_commutes_offDiagonal_product`: a reusable product consequence
  of the existing two tangent equations, with no cancellation of two.
- `E_commutes_left_E11`: the actual E commutes with the left E11 projector.
- `E_commutes_left_diagonal_difference`: E commutes with the native
  `L_map (diagonal 1 (-1))`, using its existing `2 • L_E11 - 1` identity.

The first three reuse the generic owner directly. The grading argument avoids
an extra Core.PeirceGrading dependency and any characteristic restriction.
No new Hilbert/algebra carrier, CAR bundle, star interpretation, associative
matrix-unit product law, faithfulness, or gl(3|1) classification is introduced.
The sign and order are fixed: these are products of left-action operators,
not left action of the nonassociative Zorn product.

QA must first ensure the promoted imports expose the exact inspected APIs,
then compile and audit this candidate under the shared lock. Source drafting
does not certify elaboration, axioms, or warning freedom.
