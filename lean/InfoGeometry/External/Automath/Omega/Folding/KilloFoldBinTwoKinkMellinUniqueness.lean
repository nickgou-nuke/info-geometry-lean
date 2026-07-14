import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import InfoGeometry.External.Automath.Omega.Folding.FoldBinDegeneracyTailCapacityKinks

namespace Omega.Folding

noncomputable section

def killo_fold_bin_two_kink_mellin_uniqueness_tail (c s : ℝ) : ℝ :=
  if s ≤ Real.goldenRatio⁻¹ then 1 else if s ≤ 1 then c else 0

def killo_fold_bin_two_kink_mellin_uniqueness_moment (q : Nat) (c : ℝ) : ℝ :=
  (((Real.goldenRatio⁻¹ : ℝ) ^ (q + 1)) + c * (1 - (Real.goldenRatio⁻¹ : ℝ) ^ (q + 1))) / (q + 1)

def killo_fold_bin_two_kink_mellin_uniqueness_statement (q : Nat) : Prop :=
  (∀ s,
      killo_fold_bin_two_kink_mellin_uniqueness_tail (Real.goldenRatio⁻¹) s =
        foldBinDegeneracyTailLimitFn s) ∧
    killo_fold_bin_two_kink_mellin_uniqueness_moment q (Real.goldenRatio⁻¹) =
      (((Real.goldenRatio⁻¹ : ℝ) ^ (q + 1)) +
          (Real.goldenRatio⁻¹ : ℝ) * (1 - (Real.goldenRatio⁻¹ : ℝ) ^ (q + 1))) /
        (q + 1) ∧
    ∀ c, 0 ≤ c → c ≤ 1 →
      killo_fold_bin_two_kink_mellin_uniqueness_moment q c =
        killo_fold_bin_two_kink_mellin_uniqueness_moment q (Real.goldenRatio⁻¹) →
        c = Real.goldenRatio⁻¹

private lemma killo_fold_bin_two_kink_mellin_uniqueness_phi_inv_pos :
    0 < (Real.goldenRatio⁻¹ : ℝ) := by
  positivity

private lemma killo_fold_bin_two_kink_mellin_uniqueness_phi_inv_lt_one :
    (Real.goldenRatio⁻¹ : ℝ) < 1 := by
  simpa using inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio

/-- Paper label: `thm:killo-fold-bin-two-kink-mellin-uniqueness`.
The rigid two-kink tail profile agrees with the audited limit profile, its split Mellin moment has
the closed form encoded in `killo_fold_bin_two_kink_mellin_uniqueness_moment`, and that closed form
determines the middle plateau height uniquely. -/
theorem paper_killo_fold_bin_two_kink_mellin_uniqueness (q : Nat) (hq : 0 < q) :
    killo_fold_bin_two_kink_mellin_uniqueness_statement q := by
  refine ⟨?_, rfl, ?_⟩
  · intro s
    rfl
  · intro c hc0 hc1 hmoment
    let φ : ℝ := Real.goldenRatio⁻¹
    have hφ_pos : 0 < φ := killo_fold_bin_two_kink_mellin_uniqueness_phi_inv_pos
    have hφ_lt_one : φ < 1 := killo_fold_bin_two_kink_mellin_uniqueness_phi_inv_lt_one
    have hpow_lt_one : φ ^ (q + 1) < 1 := by
      exact pow_lt_one₀ hφ_pos.le hφ_lt_one (Nat.succ_ne_zero q)
    have hfactor_ne : (1 - φ ^ (q + 1) : ℝ) ≠ 0 := by
      exact sub_ne_zero.mpr (ne_of_gt hpow_lt_one)
    have hq1_ne : (q + 1 : ℝ) ≠ 0 := by
      positivity
    have hnum : c * (1 - φ ^ (q + 1)) = φ * (1 - φ ^ (q + 1)) := by
      have hmoment_unfolded := hmoment
      unfold killo_fold_bin_two_kink_mellin_uniqueness_moment at hmoment_unfolded
      have hmoment' :
          ((φ ^ (q + 1)) + c * (1 - φ ^ (q + 1))) / (q + 1 : ℝ) =
            ((φ ^ (q + 1)) + φ * (1 - φ ^ (q + 1))) / (q + 1 : ℝ) := by
        simpa [φ] using hmoment_unfolded
      have hscaled := congrArg (fun t : ℝ => t * (q + 1 : ℝ)) hmoment'
      field_simp [hq1_ne, φ] at hscaled
      linarith
    exact mul_right_cancel₀ hfactor_ne hnum

end

end Omega.Folding
