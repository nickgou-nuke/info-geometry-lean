/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TripotentMatrixExample
import InfoGeometry.Core.TripotentIntegerGrading
import InfoGeometry.Core.TripotentJordanPair

/-!
# Nonzero integer grades and Jordan products in the existing dense matrix frame

The four-by-four owner already supplies the tripotent and its dense matrix
units. This file uses that same model to witness all five integer grades,
the two normalized opposite-extreme products, and a nonzero triple product
of the constructed Jordan pair. No second matrix model is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.TripotentIntegerStructureExample

open InfoGeometry.Physics.Algebra
open InfoGeometry.Core.TripotentAdjoint
open InfoGeometry.Core.TripotentJordanPair
open InfoGeometry.Canonical.TripotentMatrixExample

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Each of the five allowed integer grades is nonzero in the existing model. -/
theorem integerGrade_ne_bot (k : FiveGrade) :
    adGrade tripotent (fiveGradeValue k) ≠ ⊥ := by
  rw [← fiveGradeRange_eq_adGrade tripotent_cube k]
  exact fiveGradeRange_ne_bot k

/-- The dense raising unit lies in the positive extreme integer grade. -/
theorem frameUnit01_mem_posTwo : frameUnit 0 1 ∈ adGrade tripotent 2 := by
  rw [adGrade_eq_eigenspace, Module.End.mem_eigenspace_iff]
  convert ad_frameUnit 0 1 using 1
  norm_num [weight]

/-- The dense lowering unit lies in the negative extreme integer grade. -/
theorem frameUnit10_mem_negTwo : frameUnit 1 0 ∈ adGrade tripotent (-2) := by
  rw [adGrade_eq_eigenspace, Module.End.mem_eigenspace_iff]
  convert ad_frameUnit 1 0 using 1
  norm_num [weight]

/-- The opposite extreme units are normalized on the positive sector. -/
theorem frameUnit01_mul_frameUnit10 :
    frameUnit 0 1 * frameUnit 1 0 = projPos tripotent := by
  simp [frameUnit_mul, projPos_eq]

/-- The reverse normalized product is the negative-sector projector. -/
theorem frameUnit10_mul_frameUnit01 :
    frameUnit 1 0 * frameUnit 0 1 = projNeg tripotent := by
  simp [frameUnit_mul, projNeg_eq]

/-- The ordinary commutator of the normalized pair recovers its tripotent. -/
theorem opposite_extreme_lie_eq_tripotent :
    ⁅frameUnit 0 1, frameUnit 1 0⁆ = tripotent := by
  simp [Ring.lie_def, frameUnit_mul, tripotent]

/-- A concrete ordinary Jordan triple is twice the nonzero raising unit. -/
theorem extreme_lie_triple :
    ⁅⁅frameUnit 0 1, frameUnit 1 0⁆, frameUnit 0 1⁆ =
      (2 : ℝ) • frameUnit 0 1 := by
  rw [opposite_extreme_lie_eq_tripotent]
  change LieAlgebra.ad ℝ Mat tripotent (frameUnit 0 1) = _
  convert ad_frameUnit 0 1 using 1
  norm_num [weight]

theorem extreme_lie_triple_ne_zero :
    ⁅⁅frameUnit 0 1, frameUnit 1 0⁆, frameUnit 0 1⁆ ≠ 0 := by
  rw [extreme_lie_triple]
  exact smul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (frameUnit_ne_zero 0 1)

/-- The actual Jordan-pair constructor on the full ordinary matrix Lie algebra. -/
def denseJordanPair : TKKJordanPairData.JordanPair ℝ :=
  tripotentExtremeJordanPair (⊤ : LieSubalgebra ℝ Mat) tripotent tripotent_cube

/-- The positive Jordan carrier contains the dense raising unit. -/
def raising : denseJordanPair.Vplus :=
  ⟨frameUnit 0 1, ⟨by simp, frameUnit01_mem_posTwo⟩⟩

/-- The negative Jordan carrier contains the dense lowering unit. -/
def lowering : denseJordanPair.Vminus :=
  ⟨frameUnit 1 0, ⟨by simp, frameUnit10_mem_negTwo⟩⟩

/-- The triple identity holds in the constructed positive Jordan carrier. -/
theorem triplePlus_raising :
    denseJordanPair.triplePlus raising lowering raising = (2 : ℝ) • raising := by
  apply Subtype.ext
  exact extreme_lie_triple

/-- The constructed Jordan pair has a nonzero triple product. -/
theorem triplePlus_raising_ne_zero :
    denseJordanPair.triplePlus raising lowering raising ≠ 0 := by
  intro h
  apply extreme_lie_triple_ne_zero
  exact congrArg (fun X : denseJordanPair.Vplus => (X : Mat)) h

end InfoGeometry.Canonical.TripotentIntegerStructureExample
