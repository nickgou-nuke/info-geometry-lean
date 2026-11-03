/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TensorStabilizerCurvature
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Exact curvature on the tangent quotient

The quotient is a real vector-space quotient by the kernel of evaluation at
`P`. It is not asserted to be a quotient Lie algebra. The first isomorphism
law identifies it with the actual range of `D ↦ D(P)`, and the exact CE
curvature descends as the commutator of these tangent values.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorCurvatureTangentQuotient

open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Algebra.DerivationLieLane
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.Canonical.TensorLimitExactConnection
open InfoGeometry.Canonical.TensorLieStabilizerTransport
open InfoGeometry.Canonical.TensorExactCurvatureNonzero
open InfoGeometry.Examples.RealMatrixModeWitness

abbrev LimitDeriv := InfoGeometry.Algebra.NonAssocDerivation.derivations ℝ Limit

/-- Evaluate a colimit Leibniz derivation at the chosen cut. -/
def cutEvaluation (P : Limit) : LimitDeriv →ₗ[ℝ] Limit where
  toFun D := D.1 P
  map_add' D E := by rfl
  map_smul' r D := by rfl

/-- The evaluation kernel is exactly the underlying module of the native
Lie stabilizer, without claiming that this Lie subalgebra is an ideal. -/
theorem cutEvaluation_ker (P : Limit) :
    (cutEvaluation P).ker = (limitCutStabilizer P).toSubmodule := by
  ext D
  rfl

/-- The tangent quotient is linearly equivalent to the actual range of
cut evaluation. -/
def tangentQuotientEquiv (P : Limit) :
    (LimitDeriv ⧸ (cutEvaluation P).ker) ≃ₗ[ℝ] (cutEvaluation P).range :=
  (cutEvaluation P).quotKerEquivRange

/-- The bracket-valued curvature on the vector-space quotient. -/
def quotientCurvature (P : Limit)
    (u v : LimitDeriv ⧸ (cutEvaluation P).ker) : Limit :=
  (tangentQuotientEquiv P u : Limit) * (tangentQuotientEquiv P v : Limit) -
    (tangentQuotientEquiv P v : Limit) * (tangentQuotientEquiv P u : Limit)

/-- The descended expression computes the native CE curvature on arbitrary
representatives, including non-inner derivation directions. -/
theorem quotientCurvature_mk (P : Limit) (D E : LimitDeriv) :
    quotientCurvature P (Submodule.Quotient.mk D) (Submodule.Quotient.mk E) =
      connectionCurvature limitDerivationsLane
        (exteriorDerivativeZero limitDerivationsLane P) D E := by
  rw [limit_exactCurvature_all_directions]
  rfl

/-- The descended curvature is additive in the first quotient argument. -/
theorem quotientCurvature_add_left (P : Limit)
    (u v w : LimitDeriv ⧸ (cutEvaluation P).ker) :
    quotientCurvature P (u + v) w = quotientCurvature P u w + quotientCurvature P v w := by
  unfold quotientCurvature
  simp only [map_add, Submodule.coe_add, add_mul, mul_add]
  abel

/-- The descended curvature is additive in the second quotient argument. -/
theorem quotientCurvature_add_right (P : Limit)
    (u v w : LimitDeriv ⧸ (cutEvaluation P).ker) :
    quotientCurvature P u (v + w) = quotientCurvature P u v + quotientCurvature P u w := by
  unfold quotientCurvature
  simp only [map_add, Submodule.coe_add, add_mul, mul_add]
  abel

/-- The descended curvature is real-linear in its first argument. -/
theorem quotientCurvature_smul_left (P : Limit) (r : ℝ)
    (u v : LimitDeriv ⧸ (cutEvaluation P).ker) :
    quotientCurvature P (r • u) v = r • quotientCurvature P u v := by
  unfold quotientCurvature
  simp only [map_smul, Submodule.coe_smul, smul_mul_assoc, mul_smul_comm, smul_sub]

/-- The descended curvature is real-linear in its second argument. -/
theorem quotientCurvature_smul_right (P : Limit) (r : ℝ)
    (u v : LimitDeriv ⧸ (cutEvaluation P).ker) :
    quotientCurvature P u (r • v) = r • quotientCurvature P u v := by
  unfold quotientCurvature
  simp only [map_smul, Submodule.coe_smul, smul_mul_assoc, mul_smul_comm, smul_sub]

/-- The commutator expression is alternating on the tangent quotient. -/
theorem quotientCurvature_self (P : Limit)
    (u : LimitDeriv ⧸ (cutEvaluation P).ker) : quotientCurvature P u u = 0 := by
  unfold quotientCurvature
  exact sub_self _

/-- The quotient construction retains the existing nonzero dense-matrix
curvature witness in the actual colimit. -/
theorem dense_quotientCurvature_ne_zero :
    quotientCurvature (ofStage 2 p)
      (Submodule.Quotient.mk (limitInnerLieHom (ofStage 2 x)))
      (Submodule.Quotient.mk (limitInnerLieHom (ofStage 2 (star x)))) ≠ 0 := by
  rw [quotientCurvature_mk]
  exact denseMode_limitExactCurvature_ne_zero

end InfoGeometry.Canonical.TensorCurvatureTangentQuotient

end
