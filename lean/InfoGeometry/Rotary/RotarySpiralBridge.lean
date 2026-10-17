/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section
open scoped BigOperators Matrix

namespace InfoGeometry.RotarySpiralBridge

/-! ### 1. From `DiscreteRoPERepresentation.lean`: The 2D RoPE Rotor -/

/-- The 2x2 Rotary Position Embedding (RoPE) orthogonal rotor matrix for base frequency `θ`
    and sequence/phase coordinate `m`. -/
def ropeRotor (θ m : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos (m * θ), -Real.sin (m * θ);
     Real.sin (m * θ),  Real.cos (m * θ)]

@[simp]
theorem ropeRotor_zero_right (θ : ℝ) :
    ropeRotor θ 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ropeRotor]

@[simp]
theorem ropeRotor_apply_zero_zero (θ m : ℝ) :
    ropeRotor θ m 0 0 = Real.cos (m * θ) := rfl

/-- **RoPE Group Homomorphism (`ropeRotor_add`):**
    Advancing sequence position by `m₁ + m₂` multiplies the 2D RoPE rotors. -/
theorem ropeRotor_add (θ m₁ m₂ : ℝ) :
    ropeRotor θ (m₁ + m₂) = ropeRotor θ m₁ * ropeRotor θ m₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ropeRotor, Matrix.mul_apply, Fin.sum_univ_two,
          add_mul, Real.cos_add, Real.sin_add] <;> ring

/-! ### 2. From `RotaryAttentionSpiralDynamics.lean`: Loxodromic Spiral & Pitch -/

/-- The Loxodromic Metriplectic operator coupling radial damping `exp(-λ t)`
    with RoPE angular rotation `ropeRotor ω t`. -/
def loxodromicSpiralMatrix (lambda ω t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Real.exp (-lambda * t) • ropeRotor ω t

/-- Eliminating time `t = (θ - θ₀) / ω` yields the exact Logarithmic Spiral radius:
    `r(θ) = r₀ * exp(-(λ / ω) * (θ - θ₀))`. -/
def logSpiralRadius (r₀ lambda ω θ₀ θ : ℝ) : ℝ :=
  r₀ * Real.exp (-(lambda / ω) * (θ - θ₀))

/-- **Time-Elimination Bridge (`logSpiral_from_loxodromic_time`):**
    If angle advances at RoPE speed `θ = θ₀ + ω * t` (`ω ≠ 0`), the radial norm `r₀ * exp(-λ * t)`
    equals `logSpiralRadius r₀ λ ω θ₀ θ`. -/
theorem logSpiral_from_loxodromic_time
    (r₀ lambda ω θ₀ t : ℝ) (hω : ω ≠ 0) :
    r₀ * Real.exp (-lambda * t) =
      logSpiralRadius r₀ lambda ω θ₀ (θ₀ + ω * t) := by
  unfold logSpiralRadius
  congr 2
  have : θ₀ + ω * t - θ₀ = ω * t := by ring
  rw [this]
  field_simp [hω]

/-! ### 3. From `LinShuAttentionDensityWave.lean` (Archetype V):
    Multi-Head RoPE Spiral Arm Constructive Interference -/

variable {H : Type*} [Fintype H]

/-- Single-head spiral density wave contribution extracted from the `(0, 0)` axis of `ropeRotor`. -/
def ropeHeadArmWave (A : H → ℝ) (Φ : H → ℝ) (h : H) : ℝ :=
  A h * (ropeRotor 1 (Φ h) 0 0)

/-- Total multi-head spiral arm density wave across all attention heads `h : H`. -/
def multiHeadSpiralWave (A : H → ℝ) (Φ : H → ℝ) : ℝ :=
  ∑ h : H, ropeHeadArmWave A Φ h

/-- **Archetype V Theorem (`ropeHeadArmWave_constructive_interference`):**
    When all attention heads phase-lock along the spiral arm crest (`∀ h, Φ h = 0`),
    the RoPE rotors align at the identity (`cos 0 = 1`) and interfere constructively
    to achieve the coherent amplitude sum `∑ h, A h`. -/
theorem ropeHeadArmWave_constructive_interference
    (A : H → ℝ) (Φ : H → ℝ) (hLock : ∀ h : H, Φ h = 0) :
    multiHeadSpiralWave A Φ = ∑ h : H, A h := by
  unfold multiHeadSpiralWave ropeHeadArmWave
  apply Finset.sum_congr rfl
  intro h _
  rw [hLock h, ropeRotor_apply_zero_zero, zero_mul, Real.cos_zero, mul_one]

/-- **Archetype V Bound (`multiHeadSpiralWave_le_constructive_crest`):**
    For non-negative head weights `A h ≥ 0`, the multi-head RoPE wave at any phase `Φ`
    is bounded above by its constructive interference peak `∑ h, A h`. -/
theorem multiHeadSpiralWave_le_constructive_crest
    (A : H → ℝ) (Φ : H → ℝ) (hA : ∀ h : H, 0 ≤ A h) :
    multiHeadSpiralWave A Φ ≤ ∑ h : H, A h := by
  unfold multiHeadSpiralWave ropeHeadArmWave
  apply Finset.sum_le_sum
  intro h _
  rw [ropeRotor_apply_zero_zero]
  calc A h * Real.cos (Φ h * 1)
      ≤ A h * 1 := mul_le_mul_of_nonneg_left (Real.cos_le_one _) (hA h)
    _ = A h := mul_one (A h)

end InfoGeometry.RotarySpiralBridge

end
