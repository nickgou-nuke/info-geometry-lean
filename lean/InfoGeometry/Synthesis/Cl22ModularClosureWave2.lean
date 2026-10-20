/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.Cl22LightconeWeylBerezinGaugeBridge

set_option autoImplicit false

noncomputable section

open scoped Matrix
open Matrix
open InfoGeometry.Synthesis.Cl22RealDiracCarrier
open InfoGeometry.Synthesis.Cl22LightconeWeylBerezinGaugeBridge

namespace InfoGeometry.Synthesis.Cl22ModularClosureWave2

local notation "M4" => Matrix (Fin 4) (Fin 4) ℝ

/-- The Andreev rotor and its reverse transport the sheet-1 grading bivector
within its two-dimensional Clifford plane. -/
theorem andreevRotor_conjugates_omega1 (c s : ℝ) :
    andreevRotor c s * omega1 * andreevRotorRev c s =
      (c ^ 2 - s ^ 2) • omega1 + (2 * c * s) • (J_geom * omega1) := by
  have hJ_omega : J_geom * omega1 = -(omega1 * J_geom) :=
    J_geom_anticomm_omega1.2
  unfold andreevRotor andreevRotorRev
  simp only [mul_sub, add_mul, hJ_omega, smul_neg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [omega1, J_geom, e0, e1, e2] <;>
    ring

/-- Under the rotor normalization, the doubled Clifford volume element is fixed
by transport with the reverse rotor. -/
theorem normalized_andreevRotor_preserves_volumeOmega (c s : ℝ)
    (h_norm : c ^ 2 + s ^ 2 = 1) :
    andreevRotor c s * volumeOmega * andreevRotorRev c s = volumeOmega := by
  unfold andreevRotor andreevRotorRev
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [volumeOmega, omega1, omega2, J_geom, e0, e1, e2, e3,
      Matrix.mul_apply, Fin.sum_univ_four] <;>
    nlinarith [h_norm]

end InfoGeometry.Synthesis.Cl22ModularClosureWave2
