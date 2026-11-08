/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TensorQuotientCutInvolution

/-! # Weight selection for tangent quotient curvature

The idempotent's inner derivation acts as an involution on the tangent
quotient. Equivariance and evenness imply that the curvature vanishes on
pairs of equal-weight vectors. Opposite weights need not vanish.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorQuotientCurvatureWeights

set_option maxHeartbeats 1000000

open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.TensorCurvatureTangentQuotient
open InfoGeometry.Canonical.TensorTangentCurvatureGeometry
open InfoGeometry.Canonical.TensorQuotientCurvatureEquivariance
open InfoGeometry.Canonical.TensorQuotientCutInvolution
open InfoGeometry.Canonical.TensorQuotientActionWitness
open InfoGeometry.Canonical.TensorQuotientOppositeModes
open InfoGeometry.Examples.RealMatrixModeWitness

/-- The two induced cut actions cancel inside the curvature: the curvature
itself commutes with the cut. -/
theorem quotientCurvature_cut_weight_balance (P : Limit) (hP : P * P = P)
    (u v : LimitDeriv ⧸ (cutEvaluation P).ker) :
    quotientCurvature P (cutQuotientInvolution P hP u) v +
      quotientCurvature P u (cutQuotientInvolution P hP v) = 0 := by
  have hEq := quotientCurvature_stabilizer_equivariant P hP (cutInnerStabilizer P) u v
  have hZero : (cutInnerStabilizer P).1.1 (quotientCurvature P u v) = 0 := by
    change P * quotientCurvature P u v - quotientCurvature P u v * P = 0
    exact sub_eq_zero.mpr (quotientCurvature_commutes_cut P hP u v)
  change (cutInnerStabilizer P).1.1 (quotientCurvature P u v) =
    quotientCurvature P (cutQuotientInvolution P hP u) v +
      quotientCurvature P u (cutQuotientInvolution P hP v) at hEq
  exact hEq.symm.trans hZero

/-- Two `+1` weight vectors have zero mutual quotient curvature. -/
theorem quotientCurvature_positive_weights_zero (P : Limit) (hP : P * P = P)
    (u v : LimitDeriv ⧸ (cutEvaluation P).ker)
    (hu : cutQuotientInvolution P hP u = u)
    (hv : cutQuotientInvolution P hP v = v) : quotientCurvature P u v = 0 := by
  have h := quotientCurvature_cut_weight_balance P hP u v
  rw [hu, hv] at h
  have htwo : (2 : ℝ) • quotientCurvature P u v = 0 := by simpa only [two_smul] using h
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Two `-1` weight vectors have zero mutual quotient curvature. -/
theorem quotientCurvature_negative_weights_zero (P : Limit) (hP : P * P = P)
    (u v : LimitDeriv ⧸ (cutEvaluation P).ker)
    (hu : cutQuotientInvolution P hP u = -u)
    (hv : cutQuotientInvolution P hP v = -v) : quotientCurvature P u v = 0 := by
  have h := quotientCurvature_cut_weight_balance P hP u v
  rw [hu, hv] at h
  have hleft : quotientCurvature P (-u) v = -quotientCurvature P u v := by
    simpa only [neg_one_smul] using quotientCurvature_smul_left P (-1) u v
  have hright : quotientCurvature P u (-v) = -quotientCurvature P u v := by
    simpa only [neg_one_smul] using quotientCurvature_smul_right P (-1) u v
  rw [hleft, hright] at h
  have hsum : quotientCurvature P u v + quotientCurvature P u v = 0 := by
    calc
      quotientCurvature P u v + quotientCurvature P u v =
          -(-quotientCurvature P u v + -quotientCurvature P u v) := by abel
      _ = 0 := by rw [h, neg_zero]
  have htwo : (2 : ℝ) • quotientCurvature P u v = 0 := by simpa only [two_smul] using hsum
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Opposite weights can have nonzero curvature, as witnessed by the two
faithfully embedded dense noncommuting matrix modes. -/
theorem opposite_weight_curvature_nonzero :
    ∃ (u v : LimitDeriv ⧸ (cutEvaluation (ofStage 2 p)).ker),
      cutQuotientInvolution (ofStage 2 p) denseCut_idempotent u = u ∧
      cutQuotientInvolution (ofStage 2 p) denseCut_idempotent v = -v ∧
      quotientCurvature (ofStage 2 p) u v ≠ 0 := by
  exact ⟨denseQuotient, denseQuotientAdjoint, dense_opposite_weights_and_curvature.2.2.1,
    dense_opposite_weights_and_curvature.2.2.2.1, dense_opposite_weights_and_curvature.2.2.2.2⟩

end InfoGeometry.Canonical.TensorQuotientCurvatureWeights

end
