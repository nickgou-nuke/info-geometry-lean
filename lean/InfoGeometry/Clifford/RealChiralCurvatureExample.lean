/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Quantum.RealChiralCurvature
import InfoGeometry.Clifford.GullDoranPseudoscalarBridge
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A nonzero real chiral-curvature coefficient

This example uses the existing real Gull--Doran Pauli operators on `ℝ⁴`.
The phase axis `J = realPhaseAxis` has square `-1`; the actual projector is
`P = (1/2) (1 + realSigma3)`, and the self-adjoint tangent directions are
`X = realSigma1`, `Y = realSigma2`. Each commutes with `J`, while `X` and `Y`
anticommute. The full curvature is `P [X,Y] P = 2 J P`, and the real
internal-phase readout is `-2`.

The matrix carrier, phase axis and Pauli operators retain their existing
owners. No spectral sign construction, gauge-field parameter space, or
global fermion measure is asserted by this finite witness.
-/

noncomputable section

namespace InfoGeometry.Clifford.RealChiralCurvatureExample

open InfoGeometry.Clifford.GullDoranPseudoscalarBridge
open InfoGeometry.Clifford.ChiralProjectorBerryCurvature
open InfoGeometry.Quantum.RealChiralCurvature

/-- The positive spectral projector of the existing third real Pauli operator. -/
def pauliProjection : Mat4R := (1 / 2 : ℝ) • (1 + realSigma3)

theorem pauliProjection_sq : pauliProjection * pauliProjection = pauliProjection := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [pauliProjection, realSigma3, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_succ] <;> ring

theorem pauliProjection_selfAdjoint : star pauliProjection = pauliProjection := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.star_apply, pauliProjection, realSigma3]

theorem realSigma1_selfAdjoint : star realSigma1 = realSigma1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.star_apply, realSigma1]

theorem realSigma2_selfAdjoint : star realSigma2 = realSigma2 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.star_apply, realSigma2]

theorem phase_commutes_sigma1 : Commute realPhaseAxis realSigma1 := by
  change realPhaseAxis * realSigma1 = realSigma1 * realPhaseAxis
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [realPhaseAxis, realSigma1, Matrix.mul_apply, Fin.sum_univ_succ]

theorem phase_commutes_sigma2 : Commute realPhaseAxis realSigma2 := by
  change realPhaseAxis * realSigma2 = realSigma2 * realPhaseAxis
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [realPhaseAxis, realSigma2, Matrix.mul_apply, Fin.sum_univ_succ]

theorem phase_commutes_sigma3 : Commute realPhaseAxis realSigma3 := by
  change realPhaseAxis * realSigma3 = realSigma3 * realPhaseAxis
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [realPhaseAxis, realSigma3, Matrix.mul_apply, Fin.sum_univ_succ]

theorem phase_commutes_projection : Commute realPhaseAxis pauliProjection := by
  change realPhaseAxis * ((1 / 2 : ℝ) • (1 + realSigma3)) =
    ((1 / 2 : ℝ) • (1 + realSigma3)) * realPhaseAxis
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [mul_add, add_mul, mul_one, one_mul, phase_commutes_sigma3.eq]

/-- The first direction is tangent to this actual projector. -/
theorem realSigma1_tangent :
    pauliProjection * realSigma1 + realSigma1 * pauliProjection = realSigma1 := by
  unfold pauliProjection
  rw [smul_mul_assoc, mul_smul_comm, ← smul_add]
  have h : (1 + realSigma3) * realSigma1 + realSigma1 * (1 + realSigma3) =
      (2 : ℝ) • realSigma1 := by
    calc
      _ = (realSigma1 + realSigma1) +
          (realSigma1 * realSigma3 + realSigma3 * realSigma1) := by noncomm_ring
      _ = (2 : ℝ) • realSigma1 := by
        rw [realSigma1_realSigma3_anticomm, add_zero, two_smul]
  rw [h, smul_smul, div_mul_cancel₀ 1 (two_ne_zero : (2 : ℝ) ≠ 0), one_smul]

/-- The second direction is tangent to the same projector. -/
theorem realSigma2_tangent :
    pauliProjection * realSigma2 + realSigma2 * pauliProjection = realSigma2 := by
  unfold pauliProjection
  rw [smul_mul_assoc, mul_smul_comm, ← smul_add]
  have h : (1 + realSigma3) * realSigma2 + realSigma2 * (1 + realSigma3) =
      (2 : ℝ) • realSigma2 := by
    calc
      _ = (realSigma2 + realSigma2) +
          (realSigma2 * realSigma3 + realSigma3 * realSigma2) := by noncomm_ring
      _ = (2 : ℝ) • realSigma2 := by
        rw [realSigma2_realSigma3_anticomm, add_zero, two_smul]
  rw [h, smul_smul, div_mul_cancel₀ 1 (two_ne_zero : (2 : ℝ) ≠ 0), one_smul]

theorem sigma3_mul_projection : realSigma3 * pauliProjection = pauliProjection := by
  unfold pauliProjection
  rw [mul_smul_comm]
  congr 1
  rw [mul_add, mul_one, realSigma3_sq, add_comm]

/-- The full noncommutative curvature coefficient, before taking any scalar readout. -/
theorem pauli_curvature_eq :
    projectorCurvature pauliProjection realSigma1 realSigma2 =
      (2 : ℝ) • (realPhaseAxis * pauliProjection) := by
  have hproduct : realSigma1 * realSigma2 = realPhaseAxis * realSigma3 := by
    calc
      realSigma1 * realSigma2 = realSigma1 * realSigma2 * (realSigma3 * realSigma3) := by
        rw [realSigma3_sq, mul_one]
      _ = (realSigma1 * realSigma2 * realSigma3) * realSigma3 := by noncomm_ring
      _ = realPhaseAxis * realSigma3 := by rw [real_pseudoscalar_eq_phaseAxis]
  have hreverse : realSigma2 * realSigma1 = -(realSigma1 * realSigma2) := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_comm] using realSigma1_realSigma2_anticomm
  have hcomm : InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator
      realSigma1 realSigma2 =
      (2 : ℝ) • (realPhaseAxis * realSigma3) := by
    rw [InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator,
      hreverse, sub_neg_eq_add, hproduct, two_smul]
  unfold projectorCurvature
  rw [hcomm, mul_smul_comm, smul_mul_assoc]
  congr 1
  calc
    pauliProjection * (realPhaseAxis * realSigma3) * pauliProjection =
        (pauliProjection * realPhaseAxis) * (realSigma3 * pauliProjection) := by
          noncomm_ring
    _ = (realPhaseAxis * pauliProjection) * pauliProjection := by
      rw [← phase_commutes_projection.eq, sigma3_mul_projection]
    _ = realPhaseAxis * (pauliProjection * pauliProjection) := by rw [mul_assoc]
    _ = realPhaseAxis * pauliProjection := by rw [pauliProjection_sq]

theorem pauliProjection_trace : Matrix.trace pauliProjection = 2 := by
  norm_num [pauliProjection, realSigma3, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]

/-- A genuine nonzero finite real curvature readout with the paper's sign convention. -/
theorem pauli_curvature_phaseTrace :
    phaseTrace realPhaseAxis (projectorCurvature pauliProjection realSigma1 realSigma2) = -2 := by
  rw [pauli_curvature_eq]
  unfold phaseTrace
  rw [mul_smul_comm, ← mul_assoc, realPhaseAxis_sq, neg_one_mul,
    Matrix.trace_smul, Matrix.trace_neg, smul_eq_mul, pauliProjection_trace]
  norm_num

end InfoGeometry.Clifford.RealChiralCurvatureExample
