/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.Cl22RealDiracCarrier

set_option autoImplicit false
noncomputable section

open scoped Matrix
open Matrix
open InfoGeometry.Synthesis.Cl22RealDiracCarrier

namespace InfoGeometry.Synthesis.Cl22RealDiracCarrier

/-- Reverse-order normalization for the concrete `Cl(2,2)` cross-sheet rotor.
This is a carrier-level matrix identity; it makes no claim about a larger
spin group or a tensor-tower map. -/
theorem andreevRotorRev_mul_andreevRotor (c s : ℝ) :
    andreevRotorRev c s * andreevRotor c s =
      (c ^ 2 + s ^ 2) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  unfold andreevRotor andreevRotorRev
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J_geom, e0, e2, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

end InfoGeometry.Synthesis.Cl22RealDiracCarrier
