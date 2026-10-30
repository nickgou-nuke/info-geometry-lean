/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.WheelerEpilogue
import InfoGeometry.Examples.RealMatrixModeWitness

/-!
# The signed sum is not a resolution by projections

Reuses the dense full real-matrix witness already present in this PR.
No new matrix carrier or diagonal example is introduced. On its nonzero `z`,
all three double-commutator operators act as minus the identity. Consequently
the normalized signed phi combination acts as `1/8`, not as a projection.
-/

noncomputable section

namespace InfoGeometry.WheelerEpilogueWitness

attribute [local instance 100] LieRing.ofAssociativeRing

open InfoGeometry.WheelerEpilogue
open InfoGeometry.Examples.RealMatrixModeWitness
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.OperatorAlgebra.PeirceSuperoperators

local notation "F" => -((LieAlgebra.ad ℝ (Stage 2) (x + star x)) ^ 2)
local notation "G" => (LieAlgebra.ad ℝ (Stage 2) (x - star x)) ^ 2
local notation "H" => -((LieAlgebra.ad ℝ (Stage 2) ⁅x, star x⁆) ^ 2)

theorem sum_square_on_z : F z = -z := by
  have hr : z * (x + star x) = 0 := by
    rw [mul_add, z_mul_x, z_mul_star_x, add_zero]
  simp only [pow_two]
  change -⁅x + star x, ⁅x + star x, z⁆⁆ = -z
  rw [double_lie_of_right_annihilator hr,
    square_zero_pair_sum_sq x_square_zero star_x_square_zero, weight_mul_z]

theorem difference_square_on_z : G z = -z := by
  have hr : z * (x - star x) = 0 := by
    rw [mul_sub, z_mul_x, z_mul_star_x, sub_self]
  simp only [pow_two]
  change ⁅x - star x, ⁅x - star x, z⁆⁆ = -z
  rw [double_lie_of_right_annihilator hr,
    square_zero_pair_sub_sq x_square_zero star_x_square_zero, neg_mul, weight_mul_z]

theorem bracket_square_on_z : H z = -z := by
  have hl : ⁅x, star x⁆ * z = z := by
    rw [Ring.lie_def, sub_mul, x_mul_star_x, p_mul_z,
      mul_assoc, x_mul_z, mul_zero, sub_zero]
  have hr : z * ⁅x, star x⁆ = 0 := by
    rw [Ring.lie_def, mul_sub, ← mul_assoc, ← mul_assoc,
      z_mul_x, z_mul_star_x, zero_mul, zero_mul, sub_self]
  have hz : ⁅⁅x, star x⁆, z⁆ = z := by
    change ⁅x, star x⁆ * z - z * ⁅x, star x⁆ = z
    rw [hl, hr, sub_zero]
  simp only [pow_two]
  change -⁅⁅x, star x⁆, ⁅⁅x, star x⁆, z⁆⁆ = -z
  rw [hz, hz]

theorem signed_phi_on_z : (F - G - H) z = z := by
  change F z - G z - H z = z
  rw [sum_square_on_z, difference_square_on_z, bracket_square_on_z]
  abel

/-- A necessary scaled-idempotence equation already fails on the actual
nondiagonal matrix `z`. -/
theorem signed_phi_not_scaled_idempotent :
    (F - G - H) * (F - G - H) ≠ (8 : ℤ) • (F - G - H) := by
  intro heq
  have hz := congrArg (fun T : Module.End ℝ (Stage 2) => T z) heq
  change (F - G - H) ((F - G - H) z) = (8 : ℤ) • ((F - G - H) z) at hz
  simp only [signed_phi_on_z] at hz
  have he := congrArg (fun a : Stage 2 => a (((0 : Fin 1), 0), 0)
      (((0 : Fin 1), 0), 0)) hz
  norm_num [z, Matrix.smul_apply] at he

/-- Even division by eight does not turn the signed phi map into a projection. -/
theorem normalized_signed_phi_not_idempotent :
    ¬ IsIdempotentElem ((1 / 8 : ℝ) • (F - G - H)) := by
  intro hp
  have hz := congrArg (fun T : Module.End ℝ (Stage 2) => T z) hp.eq
  simp only [Module.End.mul_apply, LinearMap.smul_apply, map_smul,
    signed_phi_on_z, smul_smul] at hz
  have he := congrArg (fun a : Stage 2 => a (((0 : Fin 1), 0), 0)
      (((0 : Fin 1), 0), 0)) hz
  norm_num [z, Matrix.smul_apply] at he

end InfoGeometry.WheelerEpilogueWitness
