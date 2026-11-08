/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.ComplexMatrixJacobi
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Native derivatives of the complex matrix log-determinant potential

The potential is a real function on the full complex matrix algebra. Its
derivatives are taken over `ℝ`; invertibility is an open-domain hypothesis.
Matrix factors retain their order throughout the differential identities.
-/

noncomputable section

namespace InfoGeometry.Analysis.ComplexMatrixLogDetCalculus

open scoped Matrix Matrix.Norms.L2Operator RealInnerProductSpace ContDiff
open Matrix Filter Topology

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n ℂ

/-- The negative logarithm of determinant volume on full complex matrices. -/
def negLogDet (A : Mat) : ℝ := -Real.log ‖A.det‖

/-- Real trace as a continuous real-linear functional. -/
def realTraceCLM : Mat →L[ℝ] ℝ :=
  Complex.reCLM.comp (Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap

omit [DecidableEq n] in
@[simp] theorem realTraceCLM_apply (A : Mat) :
    realTraceCLM A = (Matrix.trace A).re := rfl

/-- The explicit continuous linear map representing the first differential. -/
def logDetDifferential (A : Mat) : Mat →L[ℝ] ℝ :=
  -(realTraceCLM.comp (ContinuousLinearMap.mul ℝ Mat A⁻¹))

@[simp] theorem logDetDifferential_apply (A H : Mat) :
    logDetDifferential A H = -(Matrix.trace (A⁻¹ * H)).re := rfl

theorem hasDerivAt_neg_log_norm_of_mul
    {f : ℝ → ℂ} {z : ℂ} {t : ℝ}
    (hf : HasDerivAt f (f t * z) t) (h0 : f t ≠ 0) :
    HasDerivAt (fun s => -Real.log ‖f s‖) (-z.re) t := by
  have hn : ‖f t‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have hi : inner ℝ (f t) (f t * z) = ‖f t‖ ^ 2 * z.re := by
    rw [Complex.inner, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply]
    ring
  have h := (hf.norm_sq.log (pow_ne_zero 2 hn)).const_mul (-1 / 2 : ℝ)
  rw [hi] at h
  convert h using 1
  · ext s
    rw [Real.log_pow]
    ring
  · field_simp

theorem differentiableAt_negLogDet {A : Mat} (hA : IsUnit A) :
    DifferentiableAt ℝ negLogDet A := by
  have hd : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).mp hA).ne_zero
  exact (((ComplexMatrixJacobi.differentiable_det A).norm ℝ hd).log
    (norm_ne_zero_iff.mpr hd)).neg

/-- The potential is smooth to every order throughout the open group of units. -/
theorem contDiffAt_negLogDet (k : ℕ∞ω) {A : Mat} (hA : IsUnit A) :
    ContDiffAt ℝ k negLogDet A := by
  have hd : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).mp hA).ne_zero
  exact ((((ComplexMatrixJacobi.contDiff_det k).contDiffAt).norm ℝ hd).log
    (norm_ne_zero_iff.mpr hd)).neg

/-- Jacobi's rule for a genuinely differentiable matrix path. -/
theorem hasDerivAt_negLogDet
    {X : ℝ → Mat} {X' : Mat} {t : ℝ}
    (hX : ∀ i j : n, HasDerivAt (fun s : ℝ => X s i j) (X' i j) t)
    (hunit : IsUnit (X t)) :
    HasDerivAt (fun s => negLogDet (X s))
      (-(Matrix.trace ((X t)⁻¹ * X')).re) t := by
  exact hasDerivAt_neg_log_norm_of_mul
    (ComplexMatrixJacobi.hasDerivAt_det hX hunit)
    ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero

theorem hasDerivAt_negLogDet_add_smul (A H : Mat) {t : ℝ}
    (hunit : IsUnit (A + t • H)) :
    HasDerivAt (fun s : ℝ => negLogDet (A + s • H))
      (-(Matrix.trace ((A + t • H)⁻¹ * H)).re) t := by
  apply hasDerivAt_negLogDet (X' := H) _ hunit
  intro i j
  simpa [Matrix.smul_apply, smul_eq_mul] using
    ((hasDerivAt_id' t).smul_const (H i j)).const_add (A i j)

theorem fderiv_negLogDet_apply (A H : Mat) (hA : IsUnit A) :
    fderiv ℝ negLogDet A H = -(Matrix.trace (A⁻¹ * H)).re := by
  have hline : HasDerivAt (fun t : ℝ => A + t • H) H 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const H).const_add A
  have hchain := (differentiableAt_negLogDet hA).hasFDerivAt
    |>.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  have hj := hasDerivAt_negLogDet_add_smul A H (t := 0) (by simpa using hA)
  simpa using hchain.unique hj

/-- Native Fréchet derivative, with every complex matrix direction available. -/
theorem hasFDerivAt_negLogDet (A : Mat) (hA : IsUnit A) :
    HasFDerivAt negLogDet (logDetDifferential A) A := by
  have h := (differentiableAt_negLogDet hA).hasFDerivAt
  convert h using 1
  ext H
  exact (fderiv_negLogDet_apply A H hA).symm

/-- The matrix inverse is differentiated in the full noncommutative algebra. -/
theorem hasFDerivAt_matrix_inv (A : Mat) (hA : IsUnit A) :
    HasFDerivAt (fun B : Mat => B⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ Mat A⁻¹ A⁻¹) A := by
  rcases hA with ⟨u, rfl⟩
  simpa only [Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit] using
    (hasFDerivAt_ringInverse (𝕜 := ℝ) u)

/-- The continuous bilinear map representing the second differential. -/
def logDetHessian (A : Mat) : Mat →L[ℝ] Mat →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ Mat Mat ℝ realTraceCLM).comp
    (ContinuousLinearMap.mul ℝ Mat)).comp
      (ContinuousLinearMap.mulLeftRight ℝ Mat A⁻¹ A⁻¹)

@[simp] theorem logDetHessian_apply (A K H : Mat) :
    logDetHessian A K H = (Matrix.trace (A⁻¹ * K * A⁻¹ * H)).re := rfl

set_option maxHeartbeats 600000 in
/-- Differentiation of the explicit first-differential field. -/
theorem hasFDerivAt_logDetDifferential (A : Mat) (hA : IsUnit A) :
    HasFDerivAt logDetDifferential (logDetHessian A) A := by
  let L : Mat →L[ℝ] Mat →L[ℝ] ℝ :=
    -((ContinuousLinearMap.compL ℝ Mat Mat ℝ realTraceCLM).comp
      (ContinuousLinearMap.mul ℝ Mat))
  have hL : HasFDerivAt (fun B : Mat => L B) L A⁻¹ := L.hasFDerivAt
  have h : HasFDerivAt (fun B : Mat => L B⁻¹)
      (L.comp (-ContinuousLinearMap.mulLeftRight ℝ Mat A⁻¹ A⁻¹)) A :=
    hL.comp (𝕜 := ℝ) (E := Mat) (F := Mat) (G := Mat →L[ℝ] ℝ)
      A (hasFDerivAt_matrix_inv A hA)
  have heq : (fun B : Mat => L B⁻¹) = logDetDifferential := rfl
  rw [heq] at h
  apply h.congr_fderiv
  ext K H
  simp [L, logDetHessian, ContinuousLinearMap.comp_apply]

/-- The native Fréchet derivative of the native first derivative.

This theorem identifies an actual Hessian, not only a declared trace form. -/
theorem hasFDerivAt_fderiv_negLogDet (A : Mat) (hA : IsUnit A) :
    HasFDerivAt (fderiv ℝ negLogDet) (logDetHessian A) A := by
  apply (hasFDerivAt_logDetDifferential A hA).congr_of_eventuallyEq
  have hu : ∀ᶠ B : Mat in 𝓝 A, IsUnit B := Units.isOpen.mem_nhds hA
  filter_upwards [hu] with B hB
  exact (hasFDerivAt_negLogDet B hB).fderiv

theorem fderiv2_negLogDet_apply (A K H : Mat) (hA : IsUnit A) :
    fderiv ℝ (fderiv ℝ negLogDet) A K H =
      (Matrix.trace (A⁻¹ * K * A⁻¹ * H)).re := by
  rw [(hasFDerivAt_fderiv_negLogDet A hA).fderiv]
  rfl

theorem logDetHessian_symmetric (A K H : Mat) :
    logDetHessian A K H = logDetHessian A H K := by
  simpa only [logDetHessian_apply, Matrix.mul_assoc] using
    congrArg Complex.re (Matrix.trace_mul_comm (A⁻¹ * K) (A⁻¹ * H))

/-- The mixed scalar readout differentiates the native first derivative. -/
theorem hasDerivAt_fderiv_negLogDet_apply_add_smul (A K H : Mat) {t : ℝ}
    (hunit : IsUnit (A + t • K)) :
    HasDerivAt (fun s : ℝ => fderiv ℝ negLogDet (A + s • K) H)
      (Matrix.trace ((A + t • K)⁻¹ * K * (A + t • K)⁻¹ * H)).re t := by
  have hline : HasDerivAt (fun s : ℝ => A + s • K) K t := by
    simpa using ((hasDerivAt_id' t).smul_const K).const_add A
  have hfield : HasDerivAt (fun s : ℝ => fderiv ℝ negLogDet (A + s • K))
      (logDetHessian (A + t • K) K) t :=
    (hasFDerivAt_fderiv_negLogDet (A + t • K) hunit).comp_hasDerivAt
      (𝕜 := ℝ) (F := Mat) (E := Mat →L[ℝ] ℝ) t hline
  simpa [Function.comp_def] using hfield.clm_apply (hasDerivAt_const t H)

theorem mixed_deriv_negLogDet_add_smul_zero (A K H : Mat) (hA : IsUnit A) :
    deriv (fun s : ℝ => fderiv ℝ negLogDet (A + s • K) H) 0 =
      (Matrix.trace (A⁻¹ * K * A⁻¹ * H)).re := by
  simpa using (hasDerivAt_fderiv_negLogDet_apply_add_smul A K H
    (t := 0) (by simpa using hA)).deriv

theorem hasDerivAt_inv_add_smul (A H : Mat) {t : ℝ}
    (hunit : IsUnit (A + t • H)) :
    HasDerivAt (fun s : ℝ => (A + s • H)⁻¹)
      (-(A + t • H)⁻¹ * H * (A + t • H)⁻¹) t := by
  have hline : HasDerivAt (fun s : ℝ => A + s • H) H t := by
    simpa using ((hasDerivAt_id' t).smul_const H).const_add A
  simpa only [Function.comp_def, _root_.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, neg_mul] using
      (hasFDerivAt_matrix_inv (A + t • H) hunit).comp_hasDerivAt t hline

theorem eventually_isUnit_add_smul (A H : Mat) {t : ℝ}
    (hunit : IsUnit (A + t • H)) :
    ∀ᶠ s : ℝ in 𝓝 t, IsUnit (A + s • H) := by
  have hc : Continuous (fun s : ℝ => A + s • H) :=
    continuous_const.add (continuous_id.smul continuous_const)
  exact hc.continuousAt.eventually (Units.isOpen.mem_nhds hunit)

/-- The derivative of the actual scalar derivative along an additive line. -/
theorem hasDerivAt_deriv_negLogDet_add_smul (A H : Mat) {t : ℝ}
    (hunit : IsUnit (A + t • H)) :
    HasDerivAt (deriv (fun s : ℝ => negLogDet (A + s • H)))
      (Matrix.trace (((A + t • H)⁻¹ * H) ^ 2)).re t := by
  have hi := hasDerivAt_inv_add_smul A H hunit
  have hr := (realTraceCLM.hasFDerivAt.comp_hasDerivAt t (hi.mul_const H)).neg
  have hraw : HasDerivAt
      (fun s : ℝ => -(Matrix.trace ((A + s • H)⁻¹ * H)).re)
      (Matrix.trace (((A + t • H)⁻¹ * H) ^ 2)).re t := by
    convert! hr using 1
    simp [pow_two, Matrix.mul_assoc]
  apply hraw.congr_of_eventuallyEq
  filter_upwards [eventually_isUnit_add_smul A H hunit] with s hs
  exact (hasDerivAt_negLogDet_add_smul A H hs).deriv

theorem second_deriv_negLogDet_add_smul (A H : Mat) {t : ℝ}
    (hunit : IsUnit (A + t • H)) :
    deriv (deriv (fun s : ℝ => negLogDet (A + s • H))) t =
      (Matrix.trace (((A + t • H)⁻¹ * H) ^ 2)).re :=
  (hasDerivAt_deriv_negLogDet_add_smul A H hunit).deriv

/-- The derivative of the actual second scalar derivative along an additive line. -/
theorem hasDerivAt_second_deriv_negLogDet_add_smul (A H : Mat) {t : ℝ}
    (hunit : IsUnit (A + t • H)) :
    HasDerivAt (deriv (deriv (fun s : ℝ => negLogDet (A + s • H))))
      (-2 * (Matrix.trace (((A + t • H)⁻¹ * H) ^ 3)).re) t := by
  have hi := (hasDerivAt_inv_add_smul A H hunit).mul_const H
  have hp := hi.mul hi
  have hr := realTraceCLM.hasFDerivAt.comp_hasDerivAt t hp
  have hraw : HasDerivAt
      (fun s : ℝ => (Matrix.trace (((A + s • H)⁻¹ * H) ^ 2)).re)
      (-2 * (Matrix.trace (((A + t • H)⁻¹ * H) ^ 3)).re) t := by
    convert hr using 1
    · ext s
      simp [pow_two]
    · simp [pow_succ, Matrix.mul_assoc, Matrix.trace_add, Matrix.trace_neg]
      ring
  apply hraw.congr_of_eventuallyEq
  filter_upwards [eventually_isUnit_add_smul A H hunit] with s hs
  exact second_deriv_negLogDet_add_smul A H hs

theorem third_deriv_negLogDet_add_smul (A H : Mat) {t : ℝ}
    (hunit : IsUnit (A + t • H)) :
    deriv (deriv (deriv (fun s : ℝ => negLogDet (A + s • H)))) t =
      -2 * (Matrix.trace (((A + t • H)⁻¹ * H) ^ 3)).re :=
  (hasDerivAt_second_deriv_negLogDet_add_smul A H hunit).deriv

theorem second_deriv_negLogDet_add_smul_zero (A H : Mat) (hA : IsUnit A) :
    deriv (deriv (fun s : ℝ => negLogDet (A + s • H))) 0 =
      (Matrix.trace ((A⁻¹ * H) ^ 2)).re := by
  simpa using second_deriv_negLogDet_add_smul A H (t := 0) (by simpa using hA)

theorem third_deriv_negLogDet_add_smul_zero (A H : Mat) (hA : IsUnit A) :
    deriv (deriv (deriv (fun s : ℝ => negLogDet (A + s • H)))) 0 =
      -2 * (Matrix.trace ((A⁻¹ * H) ^ 3)).re := by
  simpa using third_deriv_negLogDet_add_smul A H (t := 0) (by simpa using hA)

/-- Approaching a singular matrix through invertible matrices sends the potential to infinity. -/
theorem tendsto_negLogDet_at_singular {α : Type*} {l : Filter α}
    {X : α → Mat} {A : Mat} (hX : Tendsto X l (𝓝 A)) (hdet : A.det = 0)
    (hunit : ∀ᶠ x in l, IsUnit (X x)) :
    Tendsto (fun x => negLogDet (X x)) l atTop := by
  have hd : Tendsto (fun x => (X x).det) l (𝓝 A.det) :=
    ComplexMatrixJacobi.differentiable_det.continuous.continuousAt.tendsto.comp hX
  have hn : Tendsto (fun x => ‖(X x).det‖) l (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa [hdet] using hd.norm
    · filter_upwards [hunit] with x hx
      exact norm_pos_iff.mpr ((Matrix.isUnit_iff_isUnit_det _).mp hx).ne_zero
  simpa only [negLogDet, Function.comp_def] using
    tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hn)

end InfoGeometry.Analysis.ComplexMatrixLogDetCalculus
