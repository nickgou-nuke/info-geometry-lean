/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.Cl22ModularClosureWave2

set_option autoImplicit false

noncomputable section

open scoped Matrix
open Matrix
open InfoGeometry.Synthesis.Cl22RealDiracCarrier
open InfoGeometry.Synthesis.Cl22ModularClosureWave2

namespace InfoGeometry.Synthesis.Cl22NormalizedProjectorClosureWave8

local notation "M4" => Matrix (Fin 4) (Fin 4) ℝ

/-- A normalized cross-sheet rotor transports the sheet-1 positive Peirce
projector to the projector associated with the transported grading bivector. -/
theorem normalized_andreevRotor_conjugates_peircianPlus1 (c s : ℝ)
    (h_norm : c ^ 2 + s ^ 2 = 1) :
    andreevRotor c s * peircianPlus1 * andreevRotorRev c s =
      (1 / 2 : ℝ) •
        ((1 : M4) +
          ((c ^ 2 - s ^ 2) • omega1 +
            (2 * c * s) • (J_geom * omega1)))  := by
  unfold peircianPlus1
  calc
    andreevRotor c s * ((1 / 2 : ℝ) • ((1 : M4) + omega1)) *
          andreevRotorRev c s =
        (1 / 2 : ℝ) •
          (andreevRotor c s * ((1 : M4) + omega1) *
            andreevRotorRev c s) := by
              rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = (1 / 2 : ℝ) •
          (andreevRotor c s * (1 : M4) * andreevRotorRev c s +
            andreevRotor c s * omega1 * andreevRotorRev c s) := by
              simp only [mul_add, add_mul, mul_assoc]
    _ = (1 / 2 : ℝ) •
          ((1 : M4) +
            ((c ^ 2 - s ^ 2) • omega1 +
              (2 * c * s) • (J_geom * omega1))) := by
              have hprod := (andreevRotor_planar_sheet_rotation c s).1
              rw [mul_one, hprod, andreevRotor_conjugates_omega1, h_norm]
              simp


end InfoGeometry.Synthesis.Cl22NormalizedProjectorClosureWave8
