/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.NoncommutativeDiracSheetMixingAndEntropyTower
import InfoGeometry.Canonical.SplitCliffordTowerUnification
import InfoGeometry.Epistemology.IsometricCutState
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Finite Dirac-tower mass coefficient and uniform-state entropy

At stage `n`, the repository's recursively defined Dirac mass tower with unit
mass has square coefficient `n`. The existing equivalence
`clTowerEquivMatrix ℝ n` represents its carrier on a `2^n`-dimensional module;
the uniform distribution on that basis has Shannon entropy `n * log 2` nats,
or `n` bits. This identifies the finite-stage coefficient with a state-count
logarithm in bits. It does not identify the operator itself with entropy, nor
assert a continuum or thermodynamic limit.
-/

noncomputable section

namespace InfoGeometry.Canonical.DiracTowerEntropyBitsBridge

open InfoGeometry.Epistemology.IsometricCutState
open InfoGeometry.Inference.FiniteGibbs
open InfoGeometry.Algebra.NoncommutativeDiracSheetMixingAndEntropyTower

/-- The uniform state on `2^n` tower basis states has entropy `n log 2` nats. -/
theorem towerUniformProbability_entropy (n : ℕ) :
    entropyOf (uniformCutWeight (Fin (2 ^ n))) = (n : ℝ) * Real.log 2 := by
  exact uniformCutWeight_entropy_capacity (C := Fin (2 ^ n)) 2 n (by simp)

/-- Shannon entropy measured in bits for the uniform state space of the tower. -/
def towerUniformEntropyBits (n : ℕ) : ℝ :=
  entropyOf (uniformCutWeight (Fin (2 ^ n))) / Real.log 2

/-- The number of bits in the uniform `2^n`-state space is exactly `n`. -/
theorem towerUniformEntropyBits_eq_stage (n : ℕ) :
    towerUniformEntropyBits n = n := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [towerUniformEntropyBits, towerUniformProbability_entropy]
  exact mul_div_cancel_right₀ (n : ℝ) hlog

/-- For a real scalar mass `μ`, the Dirac-tower mass square has coefficient
`μ²` times the uniform state-count entropy in bits. This combines the existing
additive mass-square theorem with the finite uniform-state entropy identity. -/
theorem diracRealMass_square_eq_entropyBits_massSq (μ : ℝ) (n : ℕ) :
    diracTowerOp μ n * diracTowerOp μ n =
      InfoGeometry.Algebra.TwoSheetDiracMassEntropy.towerScalar n
        (towerUniformEntropyBits n * μ ^ 2) := by
  have hmass := (all_scales_dirac_mass_sq_additive
    (M := μ) (by simp) n).1
  rw [hmass, towerUniformEntropyBits_eq_stage]
  congr 1
  simp only [nsmul_eq_mul, star_trivial]
  ring

/-- Uniform-state entropy in bits is additive under concatenating finite
binary tower lengths. -/
theorem towerUniformEntropyBits_add (m n : ℕ) :
    towerUniformEntropyBits (m + n) =
      towerUniformEntropyBits m + towerUniformEntropyBits n := by
  simp only [towerUniformEntropyBits_eq_stage, Nat.cast_add]

end InfoGeometry.Canonical.DiracTowerEntropyBitsBridge
