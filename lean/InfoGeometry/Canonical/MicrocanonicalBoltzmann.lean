import InfoGeometry.Canonical.RenyiFromModularPowers

namespace InfoGeometry.Canonical

open Real
open Finset

/-- Boltzmann entropy of a macrostate with multiplicity Ω. -/
noncomputable def boltzmannEntropy (kB Ω : ℝ) : ℝ :=
  kB * Real.log Ω

/-- Microcanonical state: uniform distribution over Ω states. -/
noncomputable def microcanonicalState (Ω : ℕ) (i : Fin Ω) : ℝ :=
  1 / (Ω : ℝ)

/-- Theorem: For the microcanonical state, Rényi entropy coincides with Boltzmann entropy. -/
theorem renyi_eq_boltzmann_microcanonical (kB : ℝ) (Ω : ℕ) (hΩ : 0 < (Ω : ℝ)) (s : ℝ) (hs : s ≠ 1) :
    renyiEntropy kB (microcanonicalState Ω) s = boltzmannEntropy kB (Ω : ℝ) := by
  dsimp [renyiEntropy, modularLogGenerating, spectralPartition, microcanonicalState, boltzmannEntropy]
  have h_pow : ∀ i : Fin Ω, (1 / (Ω : ℝ)) ^ s = (Ω : ℝ) ^ (-s) := by
    intro i
    rw [one_div, Real.inv_rpow (le_of_lt hΩ), Real.rpow_neg (le_of_lt hΩ)]
  have h_sum : ∑ i : Fin Ω, ((1 / (Ω : ℝ)) ^ s) = (Ω : ℝ) * (Ω : ℝ) ^ (-s) := by
    have h1 : ∑ i : Fin Ω, ((1 / (Ω : ℝ)) ^ s) = ∑ i : Fin Ω, ((Ω : ℝ) ^ (-s)) := by
      apply sum_congr rfl
      intro x _
      exact h_pow x
    rw [h1, sum_const, card_univ, Fintype.card_fin]
    simp only [nsmul_eq_mul]
  rw [h_sum]
  have h_mul_pow : (Ω : ℝ) * (Ω : ℝ) ^ (-s) = (Ω : ℝ) ^ (1 - s) := by
    have h1 : (Ω : ℝ) = (Ω : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    nth_rw 1 [h1]
    rw [← Real.rpow_add hΩ]
    rfl
  rw [h_mul_pow, Real.log_rpow hΩ]
  have h_div : kB / (1 - s) = kB * (1 - s)⁻¹ := rfl
  rw [h_div]
  have h_mul_assoc : kB * (1 - s)⁻¹ * ((1 - s) * Real.log ↑Ω) = kB * ((1 - s)⁻¹ * (1 - s)) * Real.log ↑Ω := by ring
  rw [h_mul_assoc]
  have h_inv : (1 - s)⁻¹ * (1 - s) = 1 := inv_mul_cancel₀ (sub_ne_zero.mpr hs.symm)
  rw [h_inv, mul_one]

end InfoGeometry.Canonical
