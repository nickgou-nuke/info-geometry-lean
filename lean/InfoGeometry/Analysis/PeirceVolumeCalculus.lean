/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.ComplexMatrixLogDetCalculus
import InfoGeometry.Canonical.FiniteBogoliubovFrameDeformationEntropy
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# The full-matrix differential of the quadratic log-volume potential

The scalar potential is `Φ ↦ log ‖det (1 + β • (Φ * Φ))‖` on the
open set where its matrix argument is invertible. Its Fréchet derivative
retains both ordered variations `Φ * H` and `H * Φ`. Cyclicity of the
trace, together with the proved commutation of `Φ` with its own quadratic
resolvent, reduces this scalar differential to the familiar factor `2`.

On self-adjoint matrices with `β ≥ 0`, the matrix argument is strictly
positive and the potential equals the real trace of its native CFC
logarithm. The final theorem differentiates this actual trace-log along
every self-adjoint direction. No scalar formula for the general derivative
of the operator-valued logarithm is asserted.
-/

noncomputable section

namespace InfoGeometry.Analysis.PeirceVolumeCalculus

open InfoGeometry.Analysis.ComplexMatrixLogDetCalculus
open InfoGeometry.Canonical.FiniteBogoliubovFrameDeformationEntropy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n ℂ

/-- The quadratic matrix weight, without a positivity assumption. -/
def volumeWeight (β : ℝ) (Φ : Mat) : Mat := 1 + β • (Φ * Φ)

/-- The scalar log-volume potential on the full complex matrix algebra. -/
def volumeLogDet (β : ℝ) (Φ : Mat) : ℝ :=
  -negLogDet (volumeWeight β Φ)

/-- The full differential of the matrix square keeps both multiplication orders. -/
theorem hasFDerivAt_volumeWeight (β : ℝ) (Φ : Mat) :
    HasFDerivAt (volumeWeight β)
      (β • (ContinuousLinearMap.mul ℝ Mat Φ +
        (ContinuousLinearMap.mul ℝ Mat).flip Φ)) Φ := by
  have h := (((hasFDerivAt_id (𝕜 := ℝ) Φ).mul'
    (hasFDerivAt_id (𝕜 := ℝ) Φ)).const_smul β).const_add (1 : Mat)
  refine h.congr_fderiv ?_
  ext H
  rfl

/-- The native Fréchet derivative exists in every complex matrix direction. -/
theorem hasFDerivAt_volumeLogDet (β : ℝ) (Φ : Mat)
    (hunit : IsUnit (volumeWeight β Φ)) :
    HasFDerivAt (volumeLogDet β)
      (-((logDetDifferential (volumeWeight β Φ)).comp
        (β • (ContinuousLinearMap.mul ℝ Mat Φ +
          (ContinuousLinearMap.mul ℝ Mat).flip Φ)))) Φ := by
  exact ((hasFDerivAt_negLogDet (volumeWeight β Φ) hunit).comp
    Φ (hasFDerivAt_volumeWeight β Φ)).neg

/-- Ordered chain rule for the scalar log-volume potential. -/
theorem fderiv_volumeLogDet_ordered (β : ℝ) (Φ H : Mat)
    (hunit : IsUnit (volumeWeight β Φ)) :
    fderiv ℝ (volumeLogDet β) Φ H =
      β * (Matrix.trace
        ((volumeWeight β Φ)⁻¹ * (Φ * H + H * Φ))).re := by
  rw [(hasFDerivAt_volumeLogDet β Φ hunit).fderiv]
  change -(logDetDifferential (volumeWeight β Φ)
    (β • (Φ * H + H * Φ))) = _
  rw [logDetDifferential_apply, neg_neg, mul_smul_comm]
  change realTraceCLM
      (β • ((volumeWeight β Φ)⁻¹ * (Φ * H + H * Φ))) =
    β * realTraceCLM ((volumeWeight β Φ)⁻¹ * (Φ * H + H * Φ))
  simpa only [smul_eq_mul] using
    (map_smul realTraceCLM β ((volumeWeight β Φ)⁻¹ * (Φ * H + H * Φ)))

/-- The quadratic matrix weight commutes with its generating matrix. -/
theorem volumeWeight_commute (β : ℝ) (Φ : Mat) :
    Commute (volumeWeight β Φ) Φ := by
  change (1 + β • (Φ * Φ)) * Φ = Φ * (1 + β • (Φ * Φ))
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, mul_assoc]

/-- The inverse of the quadratic weight also commutes with the generator.
This does not assert that the inverse commutes with arbitrary variations. -/
theorem volumeWeight_inv_commute (β : ℝ) (Φ : Mat)
    (hunit : IsUnit (volumeWeight β Φ)) :
    Commute (volumeWeight β Φ)⁻¹ Φ := by
  have hdet := (Matrix.isUnit_iff_isUnit_det (volumeWeight β Φ)).mp hunit
  have hleft := Matrix.nonsing_inv_mul (volumeWeight β Φ) hdet
  have hright := Matrix.mul_nonsing_inv (volumeWeight β Φ) hdet
  have hc := (volumeWeight_commute β Φ).eq
  change (volumeWeight β Φ)⁻¹ * Φ = Φ * (volumeWeight β Φ)⁻¹
  calc
    (volumeWeight β Φ)⁻¹ * Φ =
        (volumeWeight β Φ)⁻¹ * Φ *
          (volumeWeight β Φ * (volumeWeight β Φ)⁻¹) := by
      rw [hright, mul_one]
    _ = (volumeWeight β Φ)⁻¹ * (Φ * volumeWeight β Φ) *
        (volumeWeight β Φ)⁻¹ := by noncomm_ring
    _ = (volumeWeight β Φ)⁻¹ * (volumeWeight β Φ * Φ) *
        (volumeWeight β Φ)⁻¹ := by rw [← hc]
    _ = ((volumeWeight β Φ)⁻¹ * volumeWeight β Φ) * Φ *
        (volumeWeight β Φ)⁻¹ := by noncomm_ring
    _ = Φ * (volumeWeight β Φ)⁻¹ := by rw [hleft, one_mul]

/-- Cyclicity reduces the scalar differential, without commuting `H` and `Φ`. -/
theorem fderiv_volumeLogDet_trace_gradient (β : ℝ) (Φ H : Mat)
    (hunit : IsUnit (volumeWeight β Φ)) :
    fderiv ℝ (volumeLogDet β) Φ H =
      2 * β * (Matrix.trace ((volumeWeight β Φ)⁻¹ * Φ * H)).re := by
  have hc := (volumeWeight_inv_commute β Φ hunit).eq
  have hcyc :
      Matrix.trace ((volumeWeight β Φ)⁻¹ * (H * Φ)) =
        Matrix.trace ((volumeWeight β Φ)⁻¹ * Φ * H) := by
    rw [← mul_assoc, Matrix.trace_mul_cycle, ← hc]
  rw [fderiv_volumeLogDet_ordered β Φ H hunit, mul_add,
    Matrix.trace_add, hcyc, ← mul_assoc, Complex.add_re]
  ring

/-- The actual CFC logarithm of the weight commutes with the deformation.
Consequently this logarithm does not generate a nonzero commutator on `Φ`. -/
theorem log_volumeWeight_commute (β : ℝ) (Φ : Mat) :
    Commute (CFC.log (volumeWeight β Φ)) Φ := by
  exact (volumeWeight_commute β Φ).cfc_real Real.log

/-- Self-adjoint squares and nonnegative parameters make the weight strictly positive. -/
theorem volumeWeight_isStrictlyPositive (β : ℝ) (hβ : 0 ≤ β)
    (Φ : Mat) (hΦ : IsSelfAdjoint Φ) :
    IsStrictlyPositive (volumeWeight β Φ) := by
  exact isStrictlyPositive_one.add_nonneg (smul_nonneg hβ hΦ.mul_self_nonneg)

/-- On the positive cone, the scalar potential is the real trace of the CFC log. -/
theorem volumeLogDet_eq_trace_log (β : ℝ) (Φ : Mat)
    (hpos : IsStrictlyPositive (volumeWeight β Φ)) :
    volumeLogDet β Φ = (Matrix.trace (CFC.log (volumeWeight β Φ))).re := by
  simpa only [volumeLogDet, negLogDet, neg_neg] using
    (trace_log_eq_log_norm_det_of_isStrictlyPositive (volumeWeight β Φ) hpos).symm

/-- The actual trace of the CFC logarithm has the stated directional derivative
along every self-adjoint direction; no commutation between `Φ` and `H` is assumed. -/
theorem hasDerivAt_trace_log_volumeWeight (β : ℝ) (hβ : 0 ≤ β)
    (Φ H : Mat) (hΦ : IsSelfAdjoint Φ) (hH : IsSelfAdjoint H) :
    HasDerivAt
      (fun t : ℝ => (Matrix.trace (CFC.log (volumeWeight β (Φ + t • H)))).re)
      (2 * β * (Matrix.trace ((volumeWeight β Φ)⁻¹ * Φ * H)).re) 0 := by
  have hunit := (volumeWeight_isStrictlyPositive β hβ Φ hΦ).isUnit
  have hline : HasDerivAt (fun t : ℝ => Φ + t • H) H 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const H).const_add Φ
  have hchain := (hasFDerivAt_volumeLogDet β Φ hunit).differentiableAt.hasFDerivAt
    |>.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  rw [fderiv_volumeLogDet_trace_gradient β Φ H hunit] at hchain
  apply hchain.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun t =>
    (volumeLogDet_eq_trace_log β (Φ + t • H)
      (volumeWeight_isStrictlyPositive β hβ (Φ + t • H)
        (hΦ.add ((IsSelfAdjoint.all t).smul hH)))).symm

/-- The native CFC logarithm takes inversion to negation on self-adjoint units.
The inverse is the genuine matrix inverse; continuity is established on the
actual spectrum, which avoids zero by invertibility. -/
theorem log_matrix_inv (A : Mat) (hA : IsSelfAdjoint A) (hunit : IsUnit A) :
    CFC.log A⁻¹ = -CFC.log A := by
  have hzero : ∀ x ∈ spectrum ℝ A, x ≠ 0 := by
    intro x hx hxzero
    subst x
    exact spectrum.zero_notMem ℝ hunit hx
  have hinv : ContinuousOn (fun x : ℝ => x⁻¹) (spectrum ℝ A) :=
    continuousOn_id.inv₀ hzero
  have hlog : ContinuousOn Real.log
      ((fun x : ℝ => x⁻¹) '' spectrum ℝ A) := by
    apply Real.continuousOn_log.mono
    rintro x ⟨y, hy, rfl⟩
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      (inv_ne_zero (hzero y hy))
  have hinv_cfc : cfc (fun x : ℝ => x⁻¹) A = A⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse]
    exact cfc_ringInverse_id (R := ℝ) A hunit hA
  calc
    CFC.log A⁻¹ = cfc Real.log (cfc (fun x : ℝ => x⁻¹) A) := by
      rw [hinv_cfc]
      rfl
    _ = cfc (Real.log ∘ (fun x : ℝ => x⁻¹)) A :=
      (cfc_comp Real.log (fun x : ℝ => x⁻¹) A hA hlog hinv).symm
    _ = -CFC.log A := by
      simpa only [Function.comp_def, Real.log_inv, CFC.log] using
        (cfc_neg Real.log A)

/-- The volume surprisal of the inverse weight is exactly the logarithm
of the positive weight. This is an operator identity, without taking a trace. -/
theorem neg_log_volumeWeight_inv (β : ℝ) (hβ : 0 ≤ β)
    (Φ : Mat) (hΦ : IsSelfAdjoint Φ) :
    -CFC.log ((volumeWeight β Φ)⁻¹) = CFC.log (volumeWeight β Φ) := by
  have hpos := volumeWeight_isStrictlyPositive β hβ Φ hΦ
  rw [log_matrix_inv (volumeWeight β Φ) hpos.isSelfAdjoint hpos.isUnit, neg_neg]

end InfoGeometry.Analysis.PeirceVolumeCalculus
