import proofs.ValencePairEnergyLevels

/-!
# Mirror valence-pair calibration

This module records the calibration layer for the finite valence-pair
Hamiltonian.  It does not assert experimental nuclear data.  Instead it proves
the algebraic invariants that any fitted `31S/31P` or similar mirror-nucleus
calibration must satisfy:

* residuals are model minus observed level energies;
* the sum of squared residuals is nonnegative;
* mirror energy differences are antisymmetric;
* the pair-mixing trace remains the sum of the two fitted diagonal levels.

The executable SymPy/Numpy script ingests the observed levels and performs the
least-squares fit.
-/

noncomputable section

namespace MirrorValencePairCalibration

open Matrix

/-- Residual between a predicted and observed energy level. -/
def residual (predicted observed : ℝ) : ℝ :=
  predicted - observed

/-- Two-level sum of squared residuals. -/
def sse2 (predicted₁ observed₁ predicted₂ observed₂ : ℝ) : ℝ :=
  residual predicted₁ observed₁ ^ 2 + residual predicted₂ observed₂ ^ 2

theorem sse2_nonnegative
    (predicted₁ observed₁ predicted₂ observed₂ : ℝ) :
    0 ≤ sse2 predicted₁ observed₁ predicted₂ observed₂ := by
  unfold sse2
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- Mirror energy difference, e.g. `E(31S)-E(31P)` for matched levels. -/
def mirrorEnergyDifference (sulfurLevel phosphorusLevel : ℝ) : ℝ :=
  sulfurLevel - phosphorusLevel

theorem mirrorEnergyDifference_antisymm (sulfurLevel phosphorusLevel : ℝ) :
    mirrorEnergyDifference sulfurLevel phosphorusLevel =
      -mirrorEnergyDifference phosphorusLevel sulfurLevel := by
  unfold mirrorEnergyDifference
  ring

@[simp] theorem mirrorEnergyDifference_self_zero (level : ℝ) :
    mirrorEnergyDifference level level = 0 := by
  simp [mirrorEnergyDifference]

/-- A fitted two-level mirror-pair Hamiltonian is the existing pair-mixing
Hamiltonian with fitted diagonal energies and fitted flow. -/
def fittedMirrorPairHamiltonian
    (phosphorusPair sulfurPair fittedFlow : ℝ) :
    HamiltonianCoriolisLieDynamics.M2C :=
  ValencePairEnergyLevels.pairMixingHamiltonian
    phosphorusPair sulfurPair fittedFlow

@[simp] theorem fittedMirrorPairHamiltonian_trace
    (phosphorusPair sulfurPair fittedFlow : ℝ) :
    Matrix.trace
      (fittedMirrorPairHamiltonian phosphorusPair sulfurPair fittedFlow) =
        (phosphorusPair + sulfurPair : ℂ) := by
  simp [fittedMirrorPairHamiltonian]

/-- Capstone: the finite calibration algebra compiles. -/
theorem mirror_valence_pair_calibration_synthesis
    (predicted₁ observed₁ predicted₂ observed₂
      phosphorusPair sulfurPair fittedFlow : ℝ) :
    0 ≤ sse2 predicted₁ observed₁ predicted₂ observed₂ ∧
    mirrorEnergyDifference phosphorusPair sulfurPair =
      -mirrorEnergyDifference sulfurPair phosphorusPair ∧
    Matrix.trace
      (fittedMirrorPairHamiltonian phosphorusPair sulfurPair fittedFlow) =
        (phosphorusPair + sulfurPair : ℂ) := by
  constructor
  · exact sse2_nonnegative predicted₁ observed₁ predicted₂ observed₂
  constructor
  · exact mirrorEnergyDifference_antisymm phosphorusPair sulfurPair
  · exact fittedMirrorPairHamiltonian_trace phosphorusPair sulfurPair fittedFlow

end MirrorValencePairCalibration

end noncomputable section
