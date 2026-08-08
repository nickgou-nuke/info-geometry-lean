import InfoGeometry.Canonical.RenyiFromModularPowers
import InfoGeometry.Canonical.ModularLogGenerating

namespace InfoGeometry.Canonical

open Real
open Finset

/-- Boltzmann entropy of a macrostate with multiplicity Ω. -/
noncomputable def boltzmannEntropy (kB Ω : ℝ) : ℝ :=
  kB * Real.log Ω

/-- Microcanonical state: uniform distribution over Ω states. -/
noncomputable def microcanonicalState (Ω : ℕ) (i : Fin Ω) : ℝ :=
  1 / (Ω : ℝ)

noncomputable def renyiEntropy (kB : ℝ) {Ω : ℕ} (P : Fin Ω → ℝ) (s : ℝ) : ℝ :=
  kB / (1 - s) * modularLogGenerating P s

/-- Theorem: For the microcanonical state, Rényi entropy coincides with Boltzmann entropy. -/
theorem renyi_eq_boltzmann_microcanonical (kB : ℝ) (Ω : ℕ) (hΩ : 0 < (Ω : ℝ)) (s : ℝ) (hs : s ≠ 1) :
    renyiEntropy kB (microcanonicalState Ω) s = boltzmannEntropy kB (Ω : ℝ) := by
  dsimp [renyiEntropy, modularLogGenerating, spectralPartition, microcanonicalState, boltzmannEntropy]
  have h1 : (∑ i : Fin Ω, (1 / (Ω : ℝ)) ^ s) = (Ω : ℝ) * (1 / (Ω : ℝ)) ^ s := by
    simp
  rw [h1]
  have h2 : 1 / (Ω : ℝ) = (Ω : ℝ)⁻¹ := one_div (Ω : ℝ)
  rw [h2]
  have h3 : ((Ω : ℝ)⁻¹) ^ s = (Ω : ℝ) ^ (-s) := by
    have h_pos : 0 ≤ (Ω : ℝ) := hΩ.le
    calc ((Ω : ℝ)⁻¹) ^ s
      _ = ((Ω : ℝ) ^ s)⁻¹ := Real.inv_rpow h_pos s
      _ = (Ω : ℝ) ^ (-s) := (Real.rpow_neg h_pos s).symm
  rw [h3]
  have h4 : (Ω : ℝ) * (Ω : ℝ) ^ (-s) = (Ω : ℝ) ^ (1 - s) := by
    have h_pow : (Ω : ℝ) = (Ω : ℝ) ^ (1 : ℝ) := (Real.rpow_one (Ω : ℝ)).symm
    nth_rw 1 [h_pow]
    rw [← Real.rpow_add hΩ]
    have h_sub : (1 : ℝ) + -s = 1 - s := sub_eq_add_neg 1 s |>.symm
    rw [h_sub]
  rw [h4]
  have h5 : Real.log ((Ω : ℝ) ^ (1 - s)) = (1 - s) * Real.log (Ω : ℝ) := by
    exact Real.log_rpow hΩ (1 - s)
  rw [h5]
  have h_div : kB / (1 - s) = kB * (1 - s)⁻¹ := div_eq_mul_inv kB (1 - s)
  rw [h_div]
  
  have h_assoc1 : (kB * (1 - s)⁻¹) * ((1 - s) * Real.log (Ω : ℝ)) = kB * ((1 - s)⁻¹ * (1 - s) * Real.log (Ω : ℝ)) := by
    calc (kB * (1 - s)⁻¹) * ((1 - s) * Real.log (Ω : ℝ))
      _ = kB * ((1 - s)⁻¹ * ((1 - s) * Real.log (Ω : ℝ))) := mul_assoc kB (1 - s)⁻¹ ((1 - s) * Real.log (Ω : ℝ))
      _ = kB * (((1 - s)⁻¹ * (1 - s)) * Real.log (Ω : ℝ)) := by rw [← mul_assoc (1 - s)⁻¹ (1 - s) (Real.log (Ω : ℝ))]
  rw [h_assoc1]
  
  have h_inv : (1 - s)⁻¹ * (1 - s) = 1 := inv_mul_cancel₀ (sub_ne_zero.mpr hs.symm)
  rw [h_inv, one_mul]

end InfoGeometry.Canonical
