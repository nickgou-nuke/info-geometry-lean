/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitCliffordSuperVirasoroModes

/-! # Exact finite-current weights and a half-weight generator

The existing residual is evaluated without changing its original operators.
The replacement is classified on all diagonal generators of the same carrier.
-/

noncomputable section
namespace InfoGeometry.Canonical.SplitCliffordSuperVirasoroModes

open Matrix
open SplitCliffordJordanWignerTwoModeCurrent

theorem diagonal_comm_G1 (d : Fin 4 → ℝ) :
    diagonal d * G1 - G1 * diagonal d = (d 2 - d 1) • G1 := by
  change diagonal d * Jplus - Jplus * diagonal d = (d 2 - d 1) • Jplus
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Jplus, a1Dag, a2, Matrix.mul_apply, Matrix.diagonal, Matrix.vecHead, Matrix.vecTail]

/-- Classification at every real weight, using the nonzero native current. -/
theorem diagonal_comm_G1_eq_iff (d : Fin 4 → ℝ) (w : ℝ) :
    diagonal d * G1 - G1 * diagonal d = w • G1 ↔ d 2 - d 1 = w := by
  rw [diagonal_comm_G1]
  exact (smul_left_injective ℝ shifted_supercurrent_nonzero).eq_iff

theorem L0_comm_G1 : L0 * G1 - G1 * L0 = -G1 := by
  have hL : L0 = diagonal ![(1/2 : ℝ), 1/2, -(1/2), -(1/2)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [L0, Matrix.diagonal]
  rw [hL, diagonal_comm_G1]
  norm_num

theorem LG_defect_eq : LG_defect = (-3/2 : ℝ) • G1 := by
  rw [LG_defect, L0_comm_G1]
  rw [show -G1 = (-1 : ℝ) • G1 by simp, ← sub_smul]
  norm_num

/-- The existing current Cartan generator, normalized to half-weight. -/
def halfWeightGenerator : M4R := (1/4 : ℝ) • Hdiag

theorem halfWeightGenerator_comm_G1 :
    halfWeightGenerator * G1 - G1 * halfWeightGenerator = (1/2 : ℝ) • G1 := by
  change ((1/4 : ℝ) • Hdiag) * Jplus - Jplus * ((1/4 : ℝ) • Hdiag) =
    (1/2 : ℝ) • Jplus
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
  change (1/4 : ℝ) • commM4 Hdiag Jplus = _
  rw [Hdiag_comm_Jplus, smul_smul]
  norm_num

theorem halfWeightGenerator_comm_Jminus :
    halfWeightGenerator * Jminus - Jminus * halfWeightGenerator = (-1/2 : ℝ) • Jminus := by
  unfold halfWeightGenerator
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
  change (1/4 : ℝ) • commM4 Hdiag Jminus = _
  rw [Hdiag_comm_Jminus, smul_smul]
  norm_num

end InfoGeometry.Canonical.SplitCliffordSuperVirasoroModes
