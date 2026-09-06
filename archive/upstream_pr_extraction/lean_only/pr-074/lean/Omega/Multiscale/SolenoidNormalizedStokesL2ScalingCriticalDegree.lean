import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Multiscale

noncomputable section

/-- Concrete finite-level data for normalized `L²` Stokes pullback scaling. -/
structure SolenoidNormalizedStokesL2ScalingData where
  q : ℕ
  r : ℕ
  pullbackNorm : ℕ → ℝ
  baseNorm : ℝ

namespace SolenoidNormalizedStokesL2ScalingData

def scalingRatio (D : SolenoidNormalizedStokesL2ScalingData) : ℝ :=
  (D.q : ℝ) / D.r

lemma closedForm_of_scaling (D : SolenoidNormalizedStokesL2ScalingData)
    (levelZero : D.pullbackNorm 0 = D.baseNorm)
    (scaling : ∀ n, D.pullbackNorm (n + 1) =
      ((D.q : ℝ) / D.r) * D.pullbackNorm n) :
    ∀ n, D.pullbackNorm n = D.baseNorm * D.scalingRatio ^ n := by
  intro n
  induction n with
  | zero =>
      simpa [scalingRatio] using levelZero
  | succ n ih =>
      calc
        D.pullbackNorm (n + 1) = D.scalingRatio * D.pullbackNorm n := by
          simpa [scalingRatio] using scaling n
        _ = D.scalingRatio * (D.baseNorm * D.scalingRatio ^ n) := by rw [ih]
        _ = D.baseNorm * D.scalingRatio ^ (n + 1) := by
          rw [pow_succ]
          ring

lemma criticalInvariant_of_closedForm (D : SolenoidNormalizedStokesL2ScalingData)
    (hr_pos : 0 < D.r)
    (hClosed : ∀ n, D.pullbackNorm n = D.baseNorm * D.scalingRatio ^ n) :
    D.q = D.r → ∀ n, D.pullbackNorm n = D.baseNorm := by
  intro hqr n
  have hRatio : D.scalingRatio = 1 := by
    unfold scalingRatio
    rw [hqr, div_self]
    exact_mod_cast Nat.ne_of_gt hr_pos
  calc
    D.pullbackNorm n = D.baseNorm * D.scalingRatio ^ n := hClosed n
    _ = D.baseNorm := by simp [hRatio]

lemma subcriticalDecay_of_closedForm (D : SolenoidNormalizedStokesL2ScalingData)
    (hr_pos : 0 < D.r)
    (baseNorm_nonneg : 0 ≤ D.baseNorm)
    (hClosed : ∀ n, D.pullbackNorm n = D.baseNorm * D.scalingRatio ^ n) :
    D.q < D.r → D.scalingRatio < 1 ∧ ∀ n, D.pullbackNorm n ≤ D.baseNorm := by
  intro hqr
  have hr : (0 : ℝ) < D.r := by exact_mod_cast hr_pos
  have hRatioLt : D.scalingRatio < 1 := by
    unfold scalingRatio
    rw [div_lt_iff₀ hr]
    simpa using (show (D.q : ℝ) < D.r by exact_mod_cast hqr)
  have hRatioNonneg : 0 ≤ D.scalingRatio := by
    unfold scalingRatio
    positivity
  refine ⟨hRatioLt, ?_⟩
  intro n
  calc
    D.pullbackNorm n = D.baseNorm * D.scalingRatio ^ n := hClosed n
    _ ≤ D.baseNorm * 1 := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_one₀ hRatioNonneg hRatioLt.le) baseNorm_nonneg
    _ = D.baseNorm := by ring

end SolenoidNormalizedStokesL2ScalingData

/-- Finite-level pullback scaling gives the closed form and its critical/subcritical consequences. -/
theorem paper_app_solenoid_normalized_stokes_l2_scaling_critical_degree
    (D : SolenoidNormalizedStokesL2ScalingData)
    (hr_pos : 0 < D.r)
    (baseNorm_nonneg : 0 ≤ D.baseNorm)
    (levelZero : D.pullbackNorm 0 = D.baseNorm)
    (scaling : ∀ n, D.pullbackNorm (n + 1) =
      ((D.q : ℝ) / D.r) * D.pullbackNorm n) :
    (∀ n, D.pullbackNorm n = D.baseNorm * D.scalingRatio ^ n) ∧
      (D.q = D.r → ∀ n, D.pullbackNorm n = D.baseNorm) ∧
        (D.q < D.r → D.scalingRatio < 1 ∧ ∀ n, D.pullbackNorm n ≤ D.baseNorm) := by
  have hClosed := SolenoidNormalizedStokesL2ScalingData.closedForm_of_scaling D levelZero scaling
  exact ⟨hClosed,
    SolenoidNormalizedStokesL2ScalingData.criticalInvariant_of_closedForm D hr_pos hClosed,
    SolenoidNormalizedStokesL2ScalingData.subcriticalDecay_of_closedForm D hr_pos
      baseNorm_nonneg hClosed⟩

end

end Omega.Multiscale
