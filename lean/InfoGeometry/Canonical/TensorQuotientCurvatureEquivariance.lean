/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TensorTangentStabilizerAction

/-! # Stabilizer equivariance of quotient curvature

The stabilizer action on the tangent module transports through the canonical
linear equivalence to the vector quotient. The descended exact curvature is
an equivariant alternating bilinear map with values in the operator algebra.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorQuotientCurvatureEquivariance

set_option maxHeartbeats 1000000
attribute [local instance 100] LieRing.ofAssociativeRing

open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.TensorLieStabilizerTransport
open InfoGeometry.Canonical.TensorCurvatureTangentQuotient
open InfoGeometry.Canonical.TensorIdempotentTangentRange
open InfoGeometry.Canonical.TensorTangentStabilizerAction

/-- The stabilizer endomorphism transported to the vector quotient by the
canonical quotient-to-tangent equivalence. -/
def quotientStabilizerAction (P : Limit) (hP : P * P = P)
    (S : limitCutStabilizer P) :
    (LimitDeriv ⧸ (cutEvaluation P).ker) →ₗ[ℝ] (LimitDeriv ⧸ (cutEvaluation P).ker) :=
  (quotientEquivIdempotentTangent P hP).symm.toLinearMap.comp
    ((stabilizerTangentAction P S).comp (quotientEquivIdempotentTangent P hP).toLinearMap)

/-- The stabilizer acts on the vector quotient through a native Lie
homomorphism, transported by Mathlib's endomorphism conjugation. -/
def quotientStabilizerLieHom (P : Limit) (hP : P * P = P) :
    limitCutStabilizer P →ₗ⁅ℝ⁆ Module.End ℝ (LimitDeriv ⧸ (cutEvaluation P).ker) :=
  (quotientEquivIdempotentTangent P hP).symm.lieConj.toLieHom.comp
    (stabilizerTangentLieHom P)

/-- The native Lie representation is the previously constructed transported
linear action. -/
theorem quotientStabilizerLieHom_apply (P : Limit) (hP : P * P = P)
    (S : limitCutStabilizer P) :
    quotientStabilizerLieHom P hP S = quotientStabilizerAction P hP S := by
  rfl

/-- The transported action agrees with the stabilizer action on tangent
operators under the quotient-to-tangent equivalence. -/
theorem quotientAction_tangent (P : Limit) (hP : P * P = P)
    (S : limitCutStabilizer P) (u : LimitDeriv ⧸ (cutEvaluation P).ker) :
    quotientEquivIdempotentTangent P hP (quotientStabilizerAction P hP S u) =
      stabilizerTangentAction P S (quotientEquivIdempotentTangent P hP u) := by
  exact (quotientEquivIdempotentTangent P hP).apply_symm_apply _

/-- The quotient curvature intertwines the stabilizer action on its two
arguments with the original derivation action on the operator algebra. -/
theorem quotientCurvature_stabilizer_equivariant (P : Limit) (hP : P * P = P)
    (S : limitCutStabilizer P) (u v : LimitDeriv ⧸ (cutEvaluation P).ker) :
    S.1.1 (quotientCurvature P u v) =
      quotientCurvature P (quotientStabilizerAction P hP S u) v +
        quotientCurvature P u (quotientStabilizerAction P hP S v) := by
  rw [quotientCurvature_eq_tangent_commutator P hP,
    quotientCurvature_eq_tangent_commutator P hP,
    quotientCurvature_eq_tangent_commutator P hP,
    quotientAction_tangent, quotientAction_tangent]
  change S.1.1 ((quotientEquivIdempotentTangent P hP u : Limit) *
      (quotientEquivIdempotentTangent P hP v : Limit) -
      (quotientEquivIdempotentTangent P hP v : Limit) *
      (quotientEquivIdempotentTangent P hP u : Limit)) = _
  rw [map_sub, S.1.property, S.1.property]
  change _ = (S.1.1 (quotientEquivIdempotentTangent P hP u : Limit) *
      (quotientEquivIdempotentTangent P hP v : Limit) -
      (quotientEquivIdempotentTangent P hP v : Limit) *
      S.1.1 (quotientEquivIdempotentTangent P hP u : Limit)) +
    ((quotientEquivIdempotentTangent P hP u : Limit) *
      S.1.1 (quotientEquivIdempotentTangent P hP v : Limit) -
      S.1.1 (quotientEquivIdempotentTangent P hP v : Limit) *
      (quotientEquivIdempotentTangent P hP u : Limit))
  abel

end InfoGeometry.Canonical.TensorQuotientCurvatureEquivariance

end
