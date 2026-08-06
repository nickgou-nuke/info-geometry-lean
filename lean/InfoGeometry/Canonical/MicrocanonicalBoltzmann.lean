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

noncomputable def spectralPartition {Ω : ℕ} (P : Fin Ω → ℝ) (s : ℝ) : ℝ :=
  ∑ i : Fin Ω, P i ^ s

noncomputable def modularLogGenerating {Ω : ℕ} (P : Fin Ω → ℝ) (s : ℝ) : ℝ :=
  Real.log (spectralPartition P s)

noncomputable def renyiEntropy (kB : ℝ) {Ω : ℕ} (P : Fin Ω → ℝ) (s : ℝ) : ℝ :=
  kB / (1 - s) * modularLogGenerating P s

/-- Theorem: For the microcanonical state, Rényi entropy coincides with Boltzmann entropy. -/
theorem renyi_eq_boltzmann_microcanonical (kB : ℝ) (Ω : ℕ) (hΩ : 0 < (Ω : ℝ)) (s : ℝ) (hs : s ≠ 1) :
    renyiEntropy kB (microcanonicalState Ω) s = boltzmannEntropy kB (Ω : ℝ) := by
  sorry

end InfoGeometry.Canonical
