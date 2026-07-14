/-
InfoGeometry/Exceptional/STUDatum.lean

Diagonal STU value construction.
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic.Ring
import InfoGeometry.Exceptional.Freudenthal

noncomputable section

namespace STUDatum

open InfoGeometry.Exceptional.Freudenthal

/-- The STU diagonal carrier space `ℝ ⊕ ℝ ⊕ ℝ`. -/
abbrev STUCarrier := Fin 3 → ℝ

/-- Bilinear trace pairing: `⟨x,y⟩ = x₀y₀ + x₁y₁ + x₂y₂`. -/
def stuTraceBilin : STUCarrier →ₗ[ℝ] STUCarrier →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := fun y =>
        x 0 * y 0 + x 1 * y 1 + x 2 * y 2
      map_add' := by
        intro y₁ y₂
        simp [Pi.add_apply]
        ring
      map_smul' := by
        intro c y
        simp [Pi.smul_apply]
        ring }
  map_add' := by
    intro x₁ x₂
    ext y
    simp [Pi.add_apply]
    ring
  map_smul' := by
    intro c x
    ext y
    simp [Pi.smul_apply]
    ring

/-- Cubic norm: `N(x) = x₀x₁x₂`. -/
def stuNormCubic (x : STUCarrier) : ℝ :=
  x 0 * x 1 * x 2

/-- Quadratic adjoint/cofactor: `x# = (x₁x₂, x₀x₂, x₀x₁)`. -/
def stuAdjointQuad (x : STUCarrier) : STUCarrier :=
  ![x 1 * x 2, x 0 * x 2, x 0 * x 1]

/--
Symmetric trilinear form:

`N₃(x,y,z) = (1 / 6) * Σ_{σ ∈ S₃} x_{σ₀} y_{σ₁} z_{σ₂}`.
-/
def stuNormTrilin : STUCarrier →ₗ[ℝ] STUCarrier →ₗ[ℝ] STUCarrier →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := fun y =>
        { toFun := fun z =>
            (1 / 6 : ℝ) *
              ( x 0 * y 1 * z 2
              + x 0 * z 1 * y 2
              + y 0 * x 1 * z 2
              + y 0 * z 1 * x 2
              + z 0 * x 1 * y 2
              + z 0 * y 1 * x 2 )
          map_add' := by
            intro z₁ z₂
            simp [Pi.add_apply]
            ring
          map_smul' := by
            intro c z
            simp [Pi.smul_apply]
            ring }
      map_add' := by
        intro y₁ y₂
        ext z
        simp [Pi.add_apply]
        ring
      map_smul' := by
        intro c y
        ext z
        simp [Pi.smul_apply]
        ring }
  map_add' := by
    intro x₁ x₂
    ext y z
    simp [Pi.add_apply]
    ring
  map_smul' := by
    intro c x
    ext y z
    simp [Pi.smul_apply]
    ring

/-- The concrete STU cubic Jordan datum. -/
def STU_Datum : CubicJordanDatum STUCarrier where
  traceBilin := stuTraceBilin
  trace_comm := by
    intro x y
    dsimp [stuTraceBilin]
    ring
  normCubic := stuNormCubic
  adjointQuad := stuAdjointQuad
  normTrilin := stuNormTrilin
  normTrilin_swap₁₂ := by
    intro x y z
    dsimp [stuNormTrilin]
    ring
  normTrilin_swap₂₃ := by
    intro x y z
    dsimp [stuNormTrilin]
    ring
  normTrilin_self := by
    intro x
    dsimp [stuNormTrilin, stuNormCubic]
    ring

end STUDatum
