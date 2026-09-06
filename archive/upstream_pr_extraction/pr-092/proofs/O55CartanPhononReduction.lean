import proofs.O55GradedGeneratorBasis
import proofs.TrappedHarmonicModes

/-!
# `O(5,5)` Cartan quantum numbers and phonon quasiparticle reduction

This module records the finite Lean spine behind the proposed
symmetry-adapted phonon/quasiparticle model:

* `O(5,5)` has rank `5`, hence five Cartan labels/quantum numbers;
* the full bivector generator count is `45`;
* the frozen active natural-basis sector has `15` trainable generators;
* a Cartan-resolved harmonic/quasiparticle truncation keeps five occupation
  numbers, one per Cartan direction.

No identification of these labels with nuclear phonons or learned normal modes
is formalized here.
-/

noncomputable section

namespace O55CartanPhononReduction

/-- Split orthogonal rank: `rank O(5,5) = 5`. -/
def o55CartanRank : ℕ := 5

/-- Number of Cartan quantum labels retained by the symmetry-adapted reduction. -/
def cartanQuantumNumberCount : ℕ := o55CartanRank

/-- Number of phonon normal-mode occupations in the Cartan-reduced toy model. -/
def cartanPhononModeCount : ℕ := o55CartanRank

@[simp] theorem o55_cartan_rank_eq : o55CartanRank = 5 := rfl

@[simp] theorem cartan_quantum_number_count_eq : cartanQuantumNumberCount = 5 := rfl

@[simp] theorem cartan_phonon_mode_count_eq : cartanPhononModeCount = 5 := rfl

/-- Five Cartan quantum numbers.  These are bookkeeping labels, not a physical
spectrum by themselves. -/
structure CartanQuantumNumbers where
  q₁ : ℤ
  q₂ : ℤ
  q₃ : ℤ
  q₄ : ℤ
  q₅ : ℤ
  deriving Repr

/-- Five phonon occupation numbers, one for each Cartan normal-mode label. -/
structure CartanPhononOccupation where
  n₁ : ℕ
  n₂ : ℕ
  n₃ : ℕ
  n₄ : ℕ
  n₅ : ℕ
  deriving Repr

/-- Total Cartan phonon occupation. -/
def totalOccupation (n : CartanPhononOccupation) : ℕ :=
  n.n₁ + n.n₂ + n.n₃ + n.n₄ + n.n₅

/-- Diagonal harmonic quasiparticle energy in the five Cartan directions. -/
def cartanPhononEnergy (ω : ℝ) (n : CartanPhononOccupation) : ℝ :=
  ω * ((totalOccupation n : ℝ) + (5 : ℝ) / 2)

/-- Optional charge-sector offset for Cartan-labelled quasiparticles. -/
def cartanChargeOffset (κ : ℝ) (q : CartanQuantumNumbers) : ℝ :=
  κ * ((q.q₁ * q.q₁ + q.q₂ * q.q₂ + q.q₃ * q.q₃ + q.q₄ * q.q₄ + q.q₅ * q.q₅ : ℤ) : ℝ)

/-- Toy Cartan-resolved quasiparticle energy. -/
def cartanQuasiparticleEnergy (ω κ : ℝ)
    (q : CartanQuantumNumbers) (n : CartanPhononOccupation) : ℝ :=
  cartanChargeOffset κ q + cartanPhononEnergy ω n

/-- The finite reduction arithmetic: full `45` generators, frozen active `15`,
and Cartan diagonal `5` labels/modes. -/
theorem o55_cartan_phonon_reduction_counts :
    O55GradedGeneratorBasis.fullGradedGeneratorCount = 45 ∧
    O55GradedGeneratorBasis.activeGradedGeneratorCount = 15 ∧
    o55CartanRank = 5 ∧
    cartanQuantumNumberCount = 5 ∧
    cartanPhononModeCount = 5 := by
  have hFull : O55GradedGeneratorBasis.fullGradedGeneratorCount = 45 :=
    O55GradedGeneratorBasis.full_graded_generator_count_eq
  have hActive : O55GradedGeneratorBasis.activeGradedGeneratorCount = 15 :=
    O55GradedGeneratorBasis.active_graded_generator_count_eq
  have hRank : o55CartanRank = 5 := o55_cartan_rank_eq
  have hQuantum : cartanQuantumNumberCount = 5 :=
    cartan_quantum_number_count_eq
  have hModes : cartanPhononModeCount = 5 :=
    cartan_phonon_mode_count_eq
  refine And.intro ?_ ?_
  · rw [hFull]
  · refine And.intro ?_ ?_
    · rw [hActive]
    · refine And.intro ?_ ?_
      · rw [hRank]
      · refine And.intro ?_ ?_
        · rw [hQuantum]
        · rw [hModes]

/-- The quasiparticle energy is exactly the declared charge offset plus the
five-mode harmonic energy. -/
theorem cartanQuasiparticleEnergy_decomposition (ω κ : ℝ)
    (q : CartanQuantumNumbers) (n : CartanPhononOccupation) :
    cartanQuasiparticleEnergy ω κ q n =
      cartanChargeOffset κ q + cartanPhononEnergy ω n := by
  rfl

/-- Capstone: Cartan quantum-number bookkeeping compiles. -/
theorem o55_cartan_phonon_reduction_synthesis
    (ω κ : ℝ) (q : CartanQuantumNumbers) (n : CartanPhononOccupation) :
    O55GradedGeneratorBasis.fullGradedGeneratorCount = 45 ∧
    O55GradedGeneratorBasis.activeGradedGeneratorCount = 15 ∧
    o55CartanRank = 5 ∧
    cartanQuantumNumberCount = 5 ∧
    cartanPhononModeCount = 5 ∧
    cartanQuasiparticleEnergy ω κ q n =
      cartanChargeOffset κ q + cartanPhononEnergy ω n ∧
    TrappedHarmonicModes.ModeTrapped TrappedHarmonicModes.HarmonicMode.fundamental = true ∧
    TrappedHarmonicModes.ModeTrapped TrappedHarmonicModes.HarmonicMode.firstOvertone = true ∧
    TrappedHarmonicModes.ModeTrapped TrappedHarmonicModes.HarmonicMode.secondOvertone = true := by
  have hCounts := o55_cartan_phonon_reduction_counts
  have hEnergy :
      cartanQuasiparticleEnergy ω κ q n =
        cartanChargeOffset κ q + cartanPhononEnergy ω n :=
    cartanQuasiparticleEnergy_decomposition ω κ q n
  have hFundamental :
      TrappedHarmonicModes.ModeTrapped
        TrappedHarmonicModes.HarmonicMode.fundamental = true :=
    TrappedHarmonicModes.fundamental_trapped
  have hFirst :
      TrappedHarmonicModes.ModeTrapped
        TrappedHarmonicModes.HarmonicMode.firstOvertone = true :=
    TrappedHarmonicModes.first_overtone_trapped
  have hSecond :
      TrappedHarmonicModes.ModeTrapped
        TrappedHarmonicModes.HarmonicMode.secondOvertone = true :=
    TrappedHarmonicModes.second_overtone_trapped
  refine And.intro ?_ ?_
  · rw [hCounts.1]
  · refine And.intro ?_ ?_
    · rw [hCounts.2.1]
    · refine And.intro ?_ ?_
      · rw [hCounts.2.2.1]
      · refine And.intro ?_ ?_
        · rw [hCounts.2.2.2.1]
        · refine And.intro ?_ ?_
          · rw [hCounts.2.2.2.2]
          · refine And.intro ?_ ?_
            · rw [hEnergy]
            · refine And.intro ?_ ?_
              · rw [hFundamental]
              · refine And.intro ?_ ?_
                · rw [hFirst]
                · rw [hSecond]

end O55CartanPhononReduction

end noncomputable section
