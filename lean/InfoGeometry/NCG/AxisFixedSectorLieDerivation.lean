/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.AlbertCayleyDickson
import InfoGeometry.NCG.ZornCommutator
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

/-!
# Axis-Fixed Grading Closure and Lie Derivation Restoration

Proves square-zero multiplication for the owner `±2` grade rays, and proves
that the commutator restricts to a Lie bracket on the associative x-axis
coordinate sector. This sector is contained in the `K_x` fixed locus over any
ring, but equality with that locus needs 2-torsion-freeness. These statements
concern this coordinate sector, not the full `C₃`-fixed `zornSinglet`
subalgebra.

Also proves that the Zorn commutator `[X, Y] = X*Y - Y*X` satisfies the
Leibniz derivation law and the Jacobi identity on the `K_x`-fixed sector
`quatSubalgX(A)`, restoring a genuine Lie algebra of inner derivations over
any noncommutative operator ring `A`.

No scalar diagonal or commuting-toy assumptions are used — all results hold
over any noncommutative ring `[Ring A]`. -/

namespace InfoGeometry.NCG.AxisFixedSectorLieDerivation

variable {A : Type*} [Ring A]

open InfoGeometry.Canonical.AlbertCayleyDickson
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix
open InfoGeometry.NCG.ZornCommutator

/-- The owner grade +2 ray `E₊₂(ξ) = ⟨0, 0, ⟨ξ,0,0⟩, 0⟩`. -/
def axisGradePlusTwo (ξ : A) : OpZornMatrix A :=
  opGradePlus2 ξ

/-- The owner grade -2 ray `E₋₂(η) = ⟨0, ⟨η,0,0⟩, 0, 0⟩`. -/
def axisGradeMinusTwo (η : A) : OpZornMatrix A :=
  opGradeMinus2 η

/-- The owner grade rays are square-zero under pairwise multiplication,
even for noncommuting coefficients. -/
theorem axis_grade_rays_nilpotent (ξ₁ ξ₂ η₁ η₂ : A) :
    axisGradePlusTwo ξ₁ * axisGradePlusTwo ξ₂ = 0 ∧
    axisGradeMinusTwo η₁ * axisGradeMinusTwo η₂ = 0 := by
  refine ⟨?_, ?_⟩
  · -- G₊₂ · G₊₂ = 0
    ext <;>
    simp [axisGradePlusTwo, opGradePlus2, mul_a, mul_b, mul_v, mul_w,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale]
  · -- G₋₂ · G₋₂ = 0
    ext <;>
    simp [axisGradeMinusTwo, opGradeMinus2, mul_a, mul_b, mul_v, mul_w,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale]

/-- **Leibniz Derivation Law on the x-axis coordinate sector**: The Zorn commutator satisfies
`[Q₁, Q₂ * Q₃] = [Q₁, Q₂] * Q₃ + Q₂ * [Q₁, Q₃]` on the x-axis Galois-fixed
sector `quatSubalgX(A)`, restoring the Leibniz rule that fails on the full
non-associative algebra. -/
theorem zornCommutator_leibniz_on_quatSubalgX
    (a₁ v₁ w₁ b₁ a₂ v₂ w₂ b₂ a₃ v₃ w₃ b₃ : A) :
    opCommutator (quatSubalgX a₁ v₁ w₁ b₁)
      ((quatSubalgX a₂ v₂ w₂ b₂) * (quatSubalgX a₃ v₃ w₃ b₃)) =
      opCommutator (quatSubalgX a₁ v₁ w₁ b₁) (quatSubalgX a₂ v₂ w₂ b₂) *
        (quatSubalgX a₃ v₃ w₃ b₃) +
      (quatSubalgX a₂ v₂ w₂ b₂) *
        opCommutator (quatSubalgX a₁ v₁ w₁ b₁) (quatSubalgX a₃ v₃ w₃ b₃) := by
  -- On the x-axis Galois-fixed sector, the Zorn multiplication restricts to
  -- ordinary M₂(A) matrix multiplication, which is associative.
  -- Direct componentwise computation verifies the Leibniz law.
  ext <;>
  simp [opCommutator, quatSubalgX,
    mul_a, mul_b, mul_v, mul_w,
    OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
    OpVec3.leftScale, OpVec3.rightScale] <;>
  noncomm_ring

/-- **Jacobi Identity on the x-axis coordinate sector**: The Zorn commutator satisfies
`[Q₁, [Q₂, Q₃]] + [Q₂, [Q₃, Q₁]] + [Q₃, [Q₁, Q₂]] = 0` on the x-axis Galois-fixed
sector `quatSubalgX(A)`, restoring the Jacobi identity that fails on the full
non-associative algebra. -/
theorem zornCommutator_jacobi_on_quatSubalgX
    (a₁ v₁ w₁ b₁ a₂ v₂ w₂ b₂ a₃ v₃ w₃ b₃ : A) :
    opCommutator (quatSubalgX a₁ v₁ w₁ b₁)
      (opCommutator (quatSubalgX a₂ v₂ w₂ b₂) (quatSubalgX a₃ v₃ w₃ b₃)) +
    opCommutator (quatSubalgX a₂ v₂ w₂ b₂)
      (opCommutator (quatSubalgX a₃ v₃ w₃ b₃) (quatSubalgX a₁ v₁ w₁ b₁)) +
    opCommutator (quatSubalgX a₃ v₃ w₃ b₃)
      (opCommutator (quatSubalgX a₁ v₁ w₁ b₁) (quatSubalgX a₂ v₂ w₂ b₂)) = 0 := by
  ext <;>
  simp [opCommutator, quatSubalgX,
    OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
    OpVec3.leftScale, OpVec3.rightScale] <;>
  noncomm_ring

end InfoGeometry.NCG.AxisFixedSectorLieDerivation
