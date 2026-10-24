/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TwoModeCurrentScaling

open Matrix InfoGeometry.Canonical.SplitCliffordSuperVirasoroModes

#print axioms diagonal_comm_G1
#print axioms diagonal_comm_G1_eq_iff
#print axioms L0_comm_G1
#print axioms LG_defect_eq
#print axioms halfWeightGenerator_comm_G1
#print axioms halfWeightGenerator_comm_Jminus
#print axioms shifted_supercurrent_nilpotent
#print axioms shifted_supercurrent_nonzero
#print axioms shifted_supercurrent_not_idempotent

example (a b t : ℝ) :
    diagonal ![a, t, t + 1/2, b] * G1 - G1 * diagonal ![a, t, t + 1/2, b] =
      (1/2 : ℝ) • G1 := by
  apply (diagonal_comm_G1_eq_iff _ _).mpr
  simp

example : LG_defect (2 : Fin 4) (1 : Fin 4) = -3/2 := by
  rw [LG_defect_eq]
  change ((-3/2 : ℝ) •
    InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent.Jplus) 2 1 = _
  norm_num [InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent.Jplus,
    InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent.a1Dag,
    InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent.a2,
    Matrix.mul_apply, Fin.sum_univ_four]
