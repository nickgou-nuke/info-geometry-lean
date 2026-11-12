/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.BipolarCayleyOccupation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Probability.Distributions.Beta

/-!
# The real logistic chart and the beta integral

This module extends the existing real logistic/log-odds chart by its Bochner
change-of-variables theorem.  It then transports Mathlib's normalized beta
density from `(0, 1)` to the real line.  Integrability and normalization are
proved from the native beta integral, not accepted as premises.

The closed formula is useful for the quantum cut density in §3 of Cassia,
Longhi and Zabzine, *Symplectic Cuts and Open/Closed Strings I*.  This module
only supplies the real analytic and measure-theoretic transport; no
Gromov--Witten construction is encoded here.
-/

noncomputable section

open MeasureTheory Set
open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarCayleyOccupation

namespace InfoGeometry.Analysis.LogisticBetaTransport

theorem logistic_injective : Function.Injective logistic := by
  intro x y h
  simpa only [logOdds_logistic] using congrArg logOdds h

theorem logistic_image_univ : logistic '' (Set.univ : Set ℝ) = Set.Ioo 0 1 := by
  ext p
  constructor
  · rintro ⟨c, _, rfl⟩
    exact ⟨logistic_pos c, logistic_lt_one c⟩
  · intro hp
    exact ⟨logOdds p, Set.mem_univ _, logistic_logOdds hp.1 hp.2⟩

/-- The derivative of the existing real logistic chart, proved by the native
quotient rule. -/
theorem hasDerivAt_logistic (c : ℝ) :
    HasDerivAt logistic (logistic c * (1 - logistic c)) c := by
  have hden : 1 + Real.exp c ≠ 0 := by positivity
  have hden' : HasDerivAt (fun x : ℝ => 1 + Real.exp x) (Real.exp c) c := by
    simpa using (Real.hasDerivAt_exp c).const_add 1
  have hquot : HasDerivAt logistic
      ((Real.exp c * (1 + Real.exp c) - Real.exp c * Real.exp c) /
        (1 + Real.exp c) ^ 2) c :=
    (Real.hasDerivAt_exp c).div hden' hden
  apply hquot.congr_deriv
  unfold logistic
  field_simp [hden]

theorem logistic_jacobian_pos (c : ℝ) :
    0 < logistic c * (1 - logistic c) :=
  mul_pos (logistic_pos c) (sub_pos.mpr (logistic_lt_one c))

/-- The explicit positive Jacobian gives change of variables through the
existing logistic chart, for arbitrary real Bochner integrands. -/
theorem integral_comp_logistic {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) :
    (∫ c, (logistic c * (1 - logistic c)) • f (logistic c)) =
      ∫ p in Set.Ioo (0 : ℝ) 1, f p := by
  have h := integral_image_eq_integral_abs_deriv_smul
    (s := Set.univ) (f := logistic) (f' := fun c => logistic c * (1 - logistic c))
    MeasurableSet.univ
    (fun c _ => (hasDerivAt_logistic c).hasDerivWithinAt)
    logistic_injective.injOn f
  simpa only [logistic_image_univ, abs_of_pos (logistic_jacobian_pos _), setIntegral_univ]
    using h.symm

/-- The same chart transports integrability, including endpoint singularities
of an integrand on the open unit interval. -/
theorem integrable_comp_logistic_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) :
    Integrable (fun c => (logistic c * (1 - logistic c)) • f (logistic c)) ↔
      IntegrableOn f (Set.Ioo (0 : ℝ) 1) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Set.univ) (f := logistic) (f' := fun c => logistic c * (1 - logistic c))
    MeasurableSet.univ
    (fun c _ => (hasDerivAt_logistic c).hasDerivWithinAt)
    logistic_injective.injOn f
  simpa only [logistic_image_univ, abs_of_pos (logistic_jacobian_pos _), integrableOn_univ]
    using h.symm

/-- Mathlib's real beta density is nonnegative when its two shape
parameters are positive. -/
theorem betaPDFReal_nonneg {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (p : ℝ) :
    0 ≤ ProbabilityTheory.betaPDFReal α β p := by
  by_cases hp : 0 < p ∧ p < 1
  · exact (ProbabilityTheory.betaPDFReal_pos hp.1 hp.2 hα hβ).le
  · simp only [ProbabilityTheory.betaPDFReal, ite_eq_right hp, le_refl]

/-- Bochner normalization of the existing native beta density. -/
theorem integral_betaPDFReal {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    (∫ p, ProbabilityTheory.betaPDFReal α β p) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (betaPDFReal_nonneg hα hβ))
    (ProbabilityTheory.stronglyMeasurable_betaPDFReal α β).aestronglyMeasurable]
  change (∫⁻ p, ProbabilityTheory.betaPDF α β p).toReal = 1
  rw [ProbabilityTheory.lintegral_betaPDF_eq_one hα hβ]
  simp

/-- Real Bochner integrability is a consequence of the normalization theorem. -/
theorem integrable_betaPDFReal {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Integrable (ProbabilityTheory.betaPDFReal α β) :=
  integrable_of_integral_eq_one (integral_betaPDFReal hα hβ)

theorem integral_betaPDFReal_Ioo {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    (∫ p in Set.Ioo (0 : ℝ) 1, ProbabilityTheory.betaPDFReal α β p) = 1 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_betaPDFReal hα hβ
  · intro p hp
    have hp' : ¬ (0 < p ∧ p < 1) := hp
    simp only [ProbabilityTheory.betaPDFReal, ite_eq_right hp']

/-- The normalized beta density expressed in the real logit coordinate.
The explicit factor `logistic c * (1 - logistic c)` is the proved Jacobian. -/
def betaLogitDensity (α β c : ℝ) : ℝ :=
  (logistic c * (1 - logistic c)) * ProbabilityTheory.betaPDFReal α β (logistic c)

theorem betaLogitDensity_pos {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (c : ℝ) :
    0 < betaLogitDensity α β c := by
  exact mul_pos (logistic_jacobian_pos c)
    (ProbabilityTheory.betaPDFReal_pos (logistic_pos c) (logistic_lt_one c) hα hβ)

theorem integrable_betaLogitDensity {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Integrable (betaLogitDensity α β) := by
  change Integrable (fun c : ℝ =>
    (logistic c * (1 - logistic c)) * ProbabilityTheory.betaPDFReal α β (logistic c))
  simpa only [smul_eq_mul] using
    (integrable_comp_logistic_iff (ProbabilityTheory.betaPDFReal α β)).2
      (integrable_betaPDFReal hα hβ).integrableOn

theorem integral_betaLogitDensity {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    (∫ c, betaLogitDensity α β c) = 1 := by
  calc
    (∫ c, betaLogitDensity α β c) =
        ∫ p in Set.Ioo (0 : ℝ) 1, ProbabilityTheory.betaPDFReal α β p := by
      simpa only [betaLogitDensity, smul_eq_mul] using
        integral_comp_logistic (ProbabilityTheory.betaPDFReal α β)
    _ = 1 := integral_betaPDFReal_Ioo hα hβ

/-- The elementary closed form of the transported density.  The identity
itself does not require positive parameters; positivity is required for its
probabilistic normalization. -/
theorem betaLogitDensity_eq_exp_div (α β c : ℝ) :
    betaLogitDensity α β c =
      Real.exp (α * c) /
        (ProbabilityTheory.beta α β * (1 + Real.exp c) ^ (α + β)) := by
  have hc : 0 < 1 + Real.exp c := by positivity
  have hp : 0 < logistic c ∧ logistic c < 1 := ⟨logistic_pos c, logistic_lt_one c⟩
  have hcomp : 1 - logistic c = 1 / (1 + Real.exp c) := by
    unfold logistic
    field_simp [hc.ne'] <;> ring
  calc
    betaLogitDensity α β c =
        (1 / ProbabilityTheory.beta α β) *
          (logistic c ^ (α - 1) * logistic c) *
          ((1 - logistic c) ^ (β - 1) * (1 - logistic c)) := by
      simp only [betaLogitDensity, ProbabilityTheory.betaPDFReal,
        ite_eq_left hp]
      ring
    _ = (1 / ProbabilityTheory.beta α β) *
        logistic c ^ α * (1 - logistic c) ^ β := by
      rw [Real.rpow_sub_one (logistic_pos c).ne' α,
        div_mul_cancel₀ _ (logistic_pos c).ne',
        Real.rpow_sub_one (sub_pos.mpr (logistic_lt_one c)).ne' β,
        div_mul_cancel₀ _ (sub_pos.mpr (logistic_lt_one c)).ne']
    _ = Real.exp (α * c) /
        (ProbabilityTheory.beta α β * (1 + Real.exp c) ^ (α + β)) := by
      rw [hcomp, logistic, Real.div_rpow (Real.exp_pos c).le hc.le α,
        Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) hc.le β,
        Real.one_rpow, ← Real.exp_mul, Real.rpow_add hc]
      simp only [div_eq_mul_inv, mul_inv_rev]
      rw [mul_comm c α]
      ring

end InfoGeometry.Analysis.LogisticBetaTransport
