import Mathlib.Tactic

/-!
# Fermi Level, Chemical Potential, and Gap

Finite grand-canonical fermion layer.

For a one-particle level with energy `E`, chemical potential `μ`, and inverse
temperature `β`, the shifted level is

`ξ = E - μ`.

The local fermionic grand partition factor is

`Z = 1 + exp (-β * ξ)`.

For a paired/gapped mode with gap `Δ`, the quasiparticle energy is modeled by

`sqrt (ξ^2 + Δ^2)`.

This is a finite scalar model, not a full BCS theory.
-/

noncomputable section

def shiftedFermiLevel (E μ : ℝ) : ℝ :=
  E - μ

def fermionFugacity (β E μ : ℝ) : ℝ :=
  Real.exp (-(β * shiftedFermiLevel E μ))

def fermiLevelPartition (β E μ : ℝ) : ℝ :=
  1 + fermionFugacity β E μ

def quasiparticleEnergy (E μ Δ : ℝ) : ℝ :=
  Real.sqrt ((shiftedFermiLevel E μ) ^ 2 + Δ ^ 2)

def spectralGapAtFermi (Δ : ℝ) : ℝ :=
  |Δ|

theorem shiftedFermiLevel_zero (μ : ℝ) :
    shiftedFermiLevel μ μ = 0 := by
  simp [shiftedFermiLevel]

theorem fermionFugacity_at_fermi (β μ : ℝ) :
    fermionFugacity β μ μ = 1 := by
  simp [fermionFugacity, shiftedFermiLevel]

theorem fermiLevelPartition_at_fermi (β μ : ℝ) :
    fermiLevelPartition β μ μ = 2 := by
  simp [fermiLevelPartition, fermionFugacity_at_fermi]
  norm_num

theorem quasiparticleEnergy_sq {E μ Δ : ℝ}
    (h : 0 ≤ (shiftedFermiLevel E μ) ^ 2 + Δ ^ 2) :
    (quasiparticleEnergy E μ Δ) ^ 2 =
      (shiftedFermiLevel E μ) ^ 2 + Δ ^ 2 := by
  unfold quasiparticleEnergy
  exact Real.sq_sqrt h

theorem quasiparticleEnergy_at_fermi_sq (μ Δ : ℝ) :
    (quasiparticleEnergy μ μ Δ) ^ 2 = Δ ^ 2 := by
  have hnonneg : 0 ≤ (shiftedFermiLevel μ μ) ^ 2 + Δ ^ 2 := by positivity
  rw [quasiparticleEnergy_sq hnonneg]
  simp [shiftedFermiLevel]

theorem gap_nonnegative (Δ : ℝ) :
    0 ≤ spectralGapAtFermi Δ := by
  simp [spectralGapAtFermi]

theorem zero_gap_closes_at_fermi (μ : ℝ) :
    quasiparticleEnergy μ μ 0 = 0 := by
  unfold quasiparticleEnergy shiftedFermiLevel
  simp

theorem gapped_energy_dominates_abs_gap (E μ Δ : ℝ) :
    spectralGapAtFermi Δ ≤ quasiparticleEnergy E μ Δ := by
  unfold spectralGapAtFermi quasiparticleEnergy
  have hle : Δ ^ 2 ≤ (shiftedFermiLevel E μ) ^ 2 + Δ ^ 2 := by
    nlinarith [sq_nonneg (shiftedFermiLevel E μ)]
  have habs : Real.sqrt (Δ ^ 2) = |Δ| := by
    rw [Real.sqrt_sq_eq_abs]
  rw [← habs]
  exact Real.sqrt_le_sqrt hle

/-- Consolidated finite Fermi-level/gap package. -/
theorem fermi_level_gap_synthesis :
    (∀ μ, shiftedFermiLevel μ μ = 0) ∧
    (∀ β μ, fermionFugacity β μ μ = 1) ∧
    (∀ β μ, fermiLevelPartition β μ μ = 2) ∧
    (∀ μ Δ, (quasiparticleEnergy μ μ Δ) ^ 2 = Δ ^ 2) ∧
    (∀ Δ, 0 ≤ spectralGapAtFermi Δ) ∧
    (∀ μ, quasiparticleEnergy μ μ 0 = 0) ∧
    (∀ E μ Δ, spectralGapAtFermi Δ ≤ quasiparticleEnergy E μ Δ) := by
  exact ⟨shiftedFermiLevel_zero, fermionFugacity_at_fermi,
    fermiLevelPartition_at_fermi, quasiparticleEnergy_at_fermi_sq,
    gap_nonnegative, zero_gap_closes_at_fermi, gapped_energy_dominates_abs_gap⟩

end noncomputable section
