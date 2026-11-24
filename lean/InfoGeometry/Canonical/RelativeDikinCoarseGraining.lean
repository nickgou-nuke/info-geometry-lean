/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.PositiveMatrixDikin
import InfoGeometry.Analysis.RelativeOperatorNeumann
import InfoGeometry.OperatorAlgebra.CoarseGrainingRelativeStability

/-!
# Dikin perturbations of positive operator coarse-graining

For a fixed rectangular observation map, bounds on the native Dikin quadratic
radii of two self-adjoint perturbations imply positivity of the perturbed
precision matrices and the same relative Loewner bounds on coarse precision.
The normalized inverse estimate consumes the same Dikin radius through the
native Euclidean operator-norm bound on the normalized variation.

The carrier is the full complex matrix algebra. The radius assumptions remain
explicit estimates on the input perturbations, and all results are finite-stage.
-/

noncomputable section

namespace InfoGeometry.Canonical.RelativeDikinCoarseGraining

open Matrix
open InfoGeometry.Analysis.PositiveMatrixDikin
open InfoGeometry.Analysis.RelativeOperatorNeumann
open InfoGeometry.OperatorAlgebra.PositiveCoarseGraining
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

private theorem positive_and_order_bounds_of_dikin_radius
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P H : Matrix ι ι ℂ} (hP : IsStrictlyPositive P) (hH : IsSelfAdjoint H)
    {r : ℝ} (hbound : Real.sqrt (traceQuadratic P H) ≤ r) (hr : r < 1) :
    (P + H).PosDef ∧ (1 - r) • P ≤ P + H ∧ P + H ≤ (1 + r) • P := by
  have hsmall : traceQuadratic P H < 1 := by
    simpa only [one_pow] using Real.lt_sq_of_sqrt_lt (hbound.trans_lt hr)
  have hpert : (P + H).PosDef := Matrix.isStrictlyPositive_iff_posDef.mp
    (isStrictlyPositive_add_of_traceQuadratic_lt_one hP hH hsmall)
  have hscale {a b : ℝ} (hab : a ≤ b) : a • P ≤ b • P := by
    rw [Matrix.le_iff, ← sub_smul]
    exact (Matrix.isStrictlyPositive_iff_posDef.mp hP).posSemidef.smul
      (sub_nonneg.mpr hab)
  obtain ⟨hlower, hupper⟩ := dikin_order_bounds hP hH
  exact ⟨hpert, (hscale (sub_le_sub_left hbound 1)).trans hlower,
    hupper.trans (hscale (add_le_add le_rfl hbound))⟩

/-- Dikin control of both input perturbations constructs positive perturbed
inputs and preserves the corresponding relative Loewner bounds under exact
coarse-graining. -/
theorem coarsePrecision_relative_sandwich_of_dikin
    {A DA : Matrix n n ℂ} {R DR : Matrix m m ℂ} (Q : Matrix m n ℂ)
    (hA : A.PosDef) (hR : R.PosDef)
    (hDA : IsSelfAdjoint DA) (hDR : IsSelfAdjoint DR)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hDA_radius : Real.sqrt (traceQuadratic A DA) ≤ r)
    (hDR_radius : Real.sqrt (traceQuadratic R DR) ≤ r) :
    (A + DA).PosDef ∧ (R + DR).PosDef ∧
      (1 - r) • coarsePrecision A R Q ≤ coarsePrecision (A + DA) (R + DR) Q ∧
      coarsePrecision (A + DA) (R + DR) Q ≤ (1 + r) • coarsePrecision A R Q := by
  obtain ⟨hA', hAlo, hAhi⟩ := positive_and_order_bounds_of_dikin_radius
    hA.isStrictlyPositive hDA hDA_radius hr1
  obtain ⟨hR', hRlo, hRhi⟩ := positive_and_order_bounds_of_dikin_radius
    hR.isStrictlyPositive hDR hDR_radius hr1
  have hcoarse := coarsePrecision_relative_sandwich Q hA hR hA' hR' hr hr1
    (Matrix.le_iff.mp hAlo) (Matrix.le_iff.mp hAhi)
    (Matrix.le_iff.mp hRlo) (Matrix.le_iff.mp hRhi)
  exact ⟨hA', hR', Matrix.le_iff.mpr hcoarse.1, Matrix.le_iff.mpr hcoarse.2⟩

/-- The true Dikin radius controls the actual inverse in the metric of the
positive reference matrix. The norm is the Euclidean operator norm. -/
theorem norm_normalized_inverse_le_of_dikin_radius [Nonempty n]
    {P H : Matrix n n ℂ} (hP : P.PosDef) (hH : IsSelfAdjoint H)
    {r : ℝ} (hbound : Real.sqrt (traceQuadratic P H) ≤ r) (hr : r < 1) :
    ‖P ^ (1 / 2 : ℝ) * (P + H)⁻¹ * P ^ (1 / 2 : ℝ)‖ ≤ 1 / (1 - r) := by
  have hnorm : ‖normalizedVariation P H‖ ≤ Real.sqrt (traceQuadratic P H) := by
    rw [traceQuadratic_eq_normalized hP.isStrictlyPositive]
    exact norm_le_sqrt_reTrace_sq (normalizedVariation_isHermitian P hH)
  apply matrix_norm_normalized_inverse_le hP ?_ hr
  simpa only [normalizedVariation, inverseSqrt] using hnorm.trans hbound

end InfoGeometry.Canonical.RelativeDikinCoarseGraining
