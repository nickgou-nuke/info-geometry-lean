import Mathlib.Tactic

/-!
# Holographic scale extinctions

Repaired external file: a `±1` glide phase on integer modes and the elementary
extinction theorem for odd modes satisfying `c = phase·c`.
-/

noncomputable section

namespace HolographicScaleExtinctions

/-- Fourier sign from a glide phase. -/
def glidePhase (k : ℤ) : ℂ := if Even k then 1 else -1

/-- Odd modes have phase `-1`. -/
theorem glidePhase_odd (k : ℤ) (hOdd : Odd k) : glidePhase k = -1 := by
  unfold glidePhase
  have hNotEven : ¬ Even k := by
    rcases hOdd with ⟨a, ha⟩
    intro he
    rcases he with ⟨b, hb⟩
    omega
  simp [hNotEven]

/-- If an odd mode obeys `c = -c`, its coefficient vanishes. -/
theorem boundary_extinction (k : ℤ) (c : ℂ) (hOdd : Odd k)
    (hSymmetric : c = glidePhase k * c) : c = 0 := by
  rw [glidePhase_odd k hOdd] at hSymmetric
  have h2 : (2 : ℂ) * c = 0 := by linear_combination hSymmetric
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- Integer-valued bulk state constrained by dispersion and glide symmetry. -/
structure AllowedBulkState where
  s : ℤ
  k : ℤ
  c : ℂ
  dispersion : s = k ∨ s = -k
  symmetric : c = glidePhase k * c
  nonTrivial : c ≠ 0

/-- A nonzero allowed state cannot have odd scale. -/
theorem no_odd_bulk_scales (state : AllowedBulkState) : ¬ Odd state.s := by
  intro hOdd_s
  have hOdd_k : Odd state.k := by
    rcases state.dispersion with h | h
    · rwa [← h]
    · rcases hOdd_s with ⟨a, ha⟩
      use -a - 1
      omega
  exact state.nonTrivial (boundary_extinction state.k state.c hOdd_k state.symmetric)

#check glidePhase_odd
#check boundary_extinction
#check no_odd_bulk_scales

end HolographicScaleExtinctions
