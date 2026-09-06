import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Canonical.CantorDiracZetaBrane

def CriticalLine (s : ℂ) : Prop :=
  Complex.re s = (1 / 2 : ℝ)

def cayleyZetaCoordinate (s : ℂ) : ℂ :=
  (s - 1) / s

theorem criticalLine_iff_cayleyCircle_native
    (s : ℂ) (hs : s ≠ 0) :
    (CriticalLine s ↔ ‖cayleyZetaCoordinate s‖ = 1) := by
  have hnorm : 0 < ‖s‖ := norm_pos_iff.mpr hs
  constructor
  · intro hcritical
    change s.re = (1 / 2 : ℝ) at hcritical
    rw [cayleyZetaCoordinate, norm_div]
    have hsq : ‖s - 1‖ ^ 2 = ‖s‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm]
      rw [Complex.normSq_apply, Complex.normSq_apply]
      norm_num
      nlinarith [hcritical]
    have hnum : ‖s - 1‖ = ‖s‖ := by
      nlinarith [norm_nonneg (s - 1), norm_nonneg s]
    rw [hnum]
    exact div_self (ne_of_gt hnorm)
  · intro hcircle
    change s.re = (1 / 2 : ℝ)
    have hquot : ‖s - 1‖ / ‖s‖ = 1 := by
      simpa [cayleyZetaCoordinate, norm_div] using hcircle
    have hnum : ‖s - 1‖ = ‖s‖ := by
      field_simp [ne_of_gt hnorm] at hquot
      exact hquot
    have hsq : ‖s - 1‖ ^ 2 = ‖s‖ ^ 2 := by rw [hnum]
    rw [Complex.sq_norm, Complex.sq_norm] at hsq
    rw [Complex.normSq_apply, Complex.normSq_apply] at hsq
    norm_num at hsq
    nlinarith

theorem cayleyZetaCoordinate_one_sub
    (s : ℂ) :
    cayleyZetaCoordinate (1 - s) =
      (cayleyZetaCoordinate s)⁻¹ := by
  unfold cayleyZetaCoordinate
  rw [inv_div]
  calc
    (1 - s - 1) / (1 - s) = (-s) / (1 - s) := by
      congr 1
      ring
    _ = s / (s - 1) := by
      simp only [div_eq_mul_inv]
      have hden : (s - 1)⁻¹ = -(1 - s)⁻¹ := by
        rw [show s - 1 = -(1 - s) by ring, inv_neg]
      rw [hden]
      ring

theorem cayleyZetaCoordinate_one_sub_norm
    (s : ℂ) :
    ‖cayleyZetaCoordinate (1 - s)‖ =
      ‖cayleyZetaCoordinate s‖⁻¹ := by
  rw [cayleyZetaCoordinate_one_sub s, norm_inv]

def SelfAdjointOnCriticalLine
    (selfAdjoint : ℂ → Prop) : Prop :=
  ∀ s : ℂ, selfAdjoint s ↔ CriticalLine s

theorem zetaPeriod_zero_implies_criticalLine
    (centralCharge : ℂ → ℂ)
    (selfAdjoint : ℂ → Prop)
    (hSelfAdjoint : SelfAdjointOnCriticalLine selfAdjoint)
    (hVanish : ∀ s : ℂ, centralCharge s = 0 → selfAdjoint s)
    (s : ℂ)
    (hz : centralCharge s = 0) :
    CriticalLine s := by
  exact (hSelfAdjoint s).mp (hVanish s hz)

theorem zetaPeriod_zero_implies_cayleyCircle
    (centralCharge : ℂ → ℂ)
    (selfAdjoint : ℂ → Prop)
    (hSelfAdjoint : SelfAdjointOnCriticalLine selfAdjoint)
    (hVanish : ∀ s : ℂ, centralCharge s = 0 → selfAdjoint s)
    (s : ℂ)
    (hs : s ≠ 0)
    (hz : centralCharge s = 0) :
    ‖cayleyZetaCoordinate s‖ = 1 := by
  exact (criticalLine_iff_cayleyCircle_native s hs).mp
    (zetaPeriod_zero_implies_criticalLine centralCharge selfAdjoint
      hSelfAdjoint hVanish s hz)

end InfoGeometry.Canonical.CantorDiracZetaBrane
