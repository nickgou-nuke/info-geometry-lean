/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic.LinearCombination
import InfoGeometry.SuperGrassmannian.GeneralSupercarrierDeformation

namespace InfoGeometry.SuperGrassmannian.GeneralSupercarrierDeformation

open Matrix

variable {ι₁ ι₂ : Type*} [DecidableEq ι₁] [Fintype ι₁] [DecidableEq ι₂] [Fintype ι₂]
variable {R : Type*} [CommRing R]

private theorem chiral_mode_mul_pair
    (B₁ B₂ : Matrix ι₁ ι₂ R) (C₁ C₂ : Matrix ι₂ ι₁ R) :
    chiralMode B₁ C₁ * chiralMode B₂ C₂ =
      Matrix.fromBlocks (B₁ * C₂) 0 0 (C₁ * B₂) := by
  dsimp [chiralMode]
  rw [Matrix.fromBlocks_multiply]
  simp

/-- The odd--odd graded superbracket has zero supertrace for arbitrary chiral
block operators.  This is the general block form of the odd supertrace
cancellation, using rectangular trace cyclicity. -/
theorem superTrace_chiral_superbracket_zero
    (B₁ B₂ : Matrix ι₁ ι₂ R) (C₁ C₂ : Matrix ι₂ ι₁ R) :
    superTrace (chiralMode B₁ C₁ * chiralMode B₂ C₂ +
      chiralMode B₂ C₂ * chiralMode B₁ C₁) = 0 := by
  rw [chiral_mode_mul_pair, chiral_mode_mul_pair, superTrace_add]
  dsimp [superTrace]
  rw [Matrix.trace_mul_comm B₁ C₂, Matrix.trace_mul_comm B₂ C₁]
  linear_combination

end InfoGeometry.SuperGrassmannian.GeneralSupercarrierDeformation
