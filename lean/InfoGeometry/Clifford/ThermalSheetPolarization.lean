/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.ChiralGrandCanonicalOperatorGeometry

noncomputable section

namespace InfoGeometry.Clifford.ChiralGrandCanonicalOperatorGeometry

open InfoGeometry.Clifford

/-- The normalized two-sector thermal polarization on the fixed sheet decomposition. -/
def thermalSheetPolarization (q : ℝ) : SheetOperatorMatrix :=
  ((1 + q) / 2 : ℝ) • sheetProjectorPlus +
    ((1 - q) / 2 : ℝ) • sheetProjectorMinus

/-- The thermal polarization is the affine grading expression `(1 + q K) / 2`. -/
theorem thermalSheetPolarization_eq_affine (q : ℝ) :
    thermalSheetPolarization q =
      (1 / 2 : ℝ) • ((1 : SheetOperatorMatrix) + q • sheetParity) := by
  unfold thermalSheetPolarization sheetProjectorPlus sheetProjectorMinus
  module

/-- Thermal polarization acts on the positive sheet with its positive weight. -/
theorem thermalSheetPolarization_mul_projectorPlus (q : ℝ) :
    thermalSheetPolarization q * sheetProjectorPlus =
      ((1 + q) / 2 : ℝ) • sheetProjectorPlus := by
  unfold thermalSheetPolarization
  rw [add_mul, smul_mul_assoc, smul_mul_assoc,
    sheetProjectorPlus_sq, sheetProjectors_mul_reverse,
    smul_zero, add_zero]

/-- Thermal polarization acts on the negative sheet with its negative weight. -/
theorem thermalSheetPolarization_mul_projectorMinus (q : ℝ) :
    thermalSheetPolarization q * sheetProjectorMinus =
      ((1 - q) / 2 : ℝ) • sheetProjectorMinus := by
  unfold thermalSheetPolarization
  rw [add_mul, smul_mul_assoc, smul_mul_assoc,
    sheetProjectors_mul, sheetProjectorMinus_sq,
    smul_zero, zero_add]

/-- The failure of thermal polarization to be a projector is a scalar defect. -/
theorem thermalSheetPolarization_sq_sub_self (q : ℝ) :
    thermalSheetPolarization q * thermalSheetPolarization q -
        thermalSheetPolarization q =
      ((q ^ 2 - 1) / 4 : ℝ) • (1 : SheetOperatorMatrix) := by
  unfold thermalSheetPolarization
  simp only [add_mul, smul_mul_assoc, mul_add, mul_smul_comm,
    sheetProjectorPlus_sq, sheetProjectors_mul, sheetProjectors_mul_reverse,
    sheetProjectorMinus_sq, smul_zero, zero_add, add_zero]
  calc
    ((1 + q) / 2 : ℝ) • ((1 + q) / 2 : ℝ) • sheetProjectorPlus +
          ((1 - q) / 2 : ℝ) • ((1 - q) / 2 : ℝ) • sheetProjectorMinus -
          (((1 + q) / 2 : ℝ) • sheetProjectorPlus +
            ((1 - q) / 2 : ℝ) • sheetProjectorMinus) =
        (((1 + q) / 2 : ℝ) ^ 2 - (1 + q) / 2) • sheetProjectorPlus +
          (((1 - q) / 2 : ℝ) ^ 2 - (1 - q) / 2) • sheetProjectorMinus := by
            module
    _ = ((q ^ 2 - 1) / 4 : ℝ) •
          (sheetProjectorPlus + sheetProjectorMinus) := by
            module
    _ = ((q ^ 2 - 1) / 4 : ℝ) • (1 : SheetOperatorMatrix) := by
            rw [sheetProjectors_add]

end InfoGeometry.Clifford.ChiralGrandCanonicalOperatorGeometry
