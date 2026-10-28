/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSuperoperators.MixedActions
import InfoGeometry.OperatorAlgebra.PeirceSuperoperators.MatrixParity
import InfoGeometry.OperatorAlgebra.PeirceSuperoperators.PeirceDifferential

/-!
# Full noncommutative matrix countermodels

All operators act on the full algebra `Matrix (Fin 4) (Fin 4) ℂ`. A
nondiagonal orthogonal projection supports a nonzero square-zero charge.
Its ordinary Lie/Jordan squares, mixed-difference defect and negative inner
curvature energy separate the false formulas from the actual graded Hodge law.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSuperoperators.Examples

open scoped ComplexOrder

open Matrix InfoGeometry.Core
open InfoGeometry.Core.JordanMultiplicationClosure
open InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint

attribute [local instance] LieRing.ofAssociativeRing

def projection : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1/2, 1/2, 0, 0; 1/2, 1/2, 0, 0; 0, 0, 1/2, 1/2; 0, 0, 1/2, 1/2]

def charge : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, -1, 2, -2; 1, -1, 2, -2; 0, 0, 3, -3; 0, 0, 3, -3]

def gram : Matrix (Fin 4) (Fin 4) ℂ := charge * chargeᴴ + chargeᴴ * charge

def probe : Matrix (Fin 4) (Fin 4) ℂ := Matrix.single 0 2 1

local notation "D" => LieAlgebra.ad ℂ (Matrix (Fin 4) (Fin 4) ℂ)
local notation "J" => jordanLeft (R := ℂ)

theorem projection_isStarProjection : IsStarProjection projection where
  isSelfAdjoint := by
    change projectionᴴ = projection
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [projection, conjTranspose_apply]
  isIdempotentElem := by
    change projection * projection = projection
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [projection, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

theorem projection_nondiagonal : projection 0 1 ≠ 0 := by norm_num [projection]

theorem projection_mul_charge : projection * charge = charge := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [projection, charge, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

theorem charge_mul_projection : charge * projection = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [projection, charge, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

theorem charge_ne_zero : charge ≠ 0 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) h
  norm_num [charge] at h00

theorem projection_charge_noncommute : projection * charge ≠ charge * projection := by
  rw [projection_mul_charge, charge_mul_projection]
  exact charge_ne_zero

theorem charge_adjoint_noncommute : charge * chargeᴴ ≠ chargeᴴ * charge := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) h
  norm_num [charge, Matrix.mul_apply, Matrix.vecMul, dotProduct, conjTranspose_apply, map_ofNat,
    Fin.sum_univ_succ] at h00

theorem charge_sq_zero : charge * charge = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [charge, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

theorem charge_odd : charge ∈ LinearMap.range (PeirceGrading.odd projection) := by
  rw [PeirceGrading.mem_odd_iff projection_isStarProjection.isIdempotentElem,
    projection_mul_charge, charge_mul_projection, add_zero]

theorem charge_not_reflexive : charge * chargeᴴ * charge ≠ charge := by
  intro h
  have h20 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 2 0) h
  norm_num [charge, Matrix.mul_apply, Matrix.vecMul, dotProduct, conjTranspose_apply, map_ofNat,
    Fin.sum_univ_succ] at h20

theorem ordinary_lie_square_entry : (D charge (D charge chargeᴴ)) 2 0 = -48 := by
  change (charge * (charge * chargeᴴ - chargeᴴ * charge) -
    (charge * chargeᴴ - chargeᴴ * charge) * charge) 2 0 = -48
  norm_num [charge, Matrix.mul_apply, Matrix.vecMul, dotProduct, conjTranspose_apply, map_ofNat, Fin.sum_univ_succ]

theorem ordinary_jordan_square_entry : (J charge (J charge chargeᴴ)) 2 0 = 48 := by
  change (charge * (charge * chargeᴴ + chargeᴴ * charge) +
    (charge * chargeᴴ + chargeᴴ * charge) * charge) 2 0 = 48
  norm_num [charge, Matrix.mul_apply, Matrix.vecMul, dotProduct, conjTranspose_apply, map_ofNat, Fin.sum_univ_succ]

theorem ordinary_lie_square_ne_zero : D charge * D charge ≠ 0 := by
  intro h
  have hc := congrArg (fun T : Module.End ℂ (Matrix (Fin 4) (Fin 4) ℂ) =>
    (T chargeᴴ) 2 0) h
  change (D charge (D charge chargeᴴ)) 2 0 = 0 at hc
  rw [ordinary_lie_square_entry] at hc
  norm_num at hc

theorem ordinary_jordan_square_ne_zero : J charge * J charge ≠ 0 := by
  intro h
  have hc := congrArg (fun T : Module.End ℂ (Matrix (Fin 4) (Fin 4) ℂ) =>
    (T chargeᴴ) 2 0) h
  change (J charge (J charge chargeᴴ)) 2 0 = 0 at hc
  rw [ordinary_jordan_square_entry] at hc
  norm_num at hc

theorem mixed_difference_defect :
    ((D charge * J chargeᴴ - D chargeᴴ * J charge - J ⁅charge, chargeᴴ⁆)
      projection) 2 0 = -8 := by
  rw [lie_jordan_difference, add_sub_cancel_left]
  change (2 • (charge * (projection * chargeᴴ) - chargeᴴ * (projection * charge))) 2 0 = -8
  norm_num [projection, charge, Matrix.mul_apply, Matrix.vecMul, dotProduct, conjTranspose_apply, map_ofNat,
    Fin.sum_univ_succ]

theorem mixed_difference_ne_jordan_bracket :
    D charge * J chargeᴴ - D chargeᴴ * J charge ≠ J ⁅charge, chargeᴴ⁆ := by
  intro h
  have hc := mixed_difference_defect
  rw [h, sub_self] at hc
  norm_num at hc

theorem gram_entry : gram 0 0 = 12 := by
  norm_num [gram, charge, Matrix.mul_apply, Matrix.vecMul, dotProduct, conjTranspose_apply, map_ofNat, Fin.sum_univ_succ]

theorem gram_nondiagonal : gram 0 1 = 8 := by
  norm_num [gram, charge, Matrix.mul_apply, Matrix.vecMul, dotProduct, conjTranspose_apply, map_ofNat, Fin.sum_univ_succ]

theorem gram_ne_zero : gram ≠ 0 := by
  intro h
  have hc := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) h
  rw [gram_entry] at hc
  norm_num at hc

local notation "θ" => parityEquiv (R := ℂ) projection projection_isStarProjection.isIdempotentElem

/-- The actual graded endomorphism, unlike the two ordinary ones, has square zero. -/
theorem graded_charge_square_zero : gradedAdjoint θ charge * gradedAdjoint θ charge = 0 :=
  peirce_graded_square_zero projection_isStarProjection.isIdempotentElem charge_odd charge_sq_zero

theorem identity_joint_graded_kernel :
    (1 : Matrix (Fin 4) (Fin 4) ℂ) ∈
      (gradedAdjoint θ charge).ker ⊓ (gradedAdjoint θ chargeᴴ).ker := by
  constructor <;> change gradedAdjoint θ _ 1 = 0 <;> simp only [gradedAdjoint_apply, map_one, Matrix.mul_one, Matrix.one_mul, sub_self]

theorem charge_centralizes_gram : D gram charge = 0 := by
  change (charge * chargeᴴ + chargeᴴ * charge) * charge -
    charge * (charge * chargeᴴ + chargeᴴ * charge) = 0
  have hleft : charge * (charge * chargeᴴ) = 0 := by
    rw [← mul_assoc, charge_sq_zero, zero_mul]
  simp only [add_mul, mul_add, mul_assoc, charge_sq_zero, hleft, mul_zero,
    zero_add, add_zero, sub_self]

theorem charge_not_joint_graded_kernel :
    charge ∉ (gradedAdjoint θ charge).ker ⊓ (gradedAdjoint θ chargeᴴ).ker := by
  intro h
  have hc : gradedAdjoint θ chargeᴴ charge = 0 := h.2
  rw [gradedAdjoint_of_odd θ chargeᴴ charge
    (parityEquiv_of_odd projection_isStarProjection.isIdempotentElem charge_odd)] at hc
  exact gram_ne_zero (by simpa only [gram, add_comm] using hc)

local instance : NormedAddCommGroup (Matrix (Fin 4) (Fin 4) ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance : InnerProductSpace ℂ (Matrix (Fin 4) (Fin 4) ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

theorem metric_adjoint_ne_graded_adjoint :
    (gradedAdjoint θ charge).adjoint ≠ gradedAdjoint θ chargeᴴ := by
  intro h
  have hc : (gradedAdjoint θ charge).adjoint (1 : Matrix (Fin 4) (Fin 4) ℂ) = 0 := by
    rw [h]
    simp only [gradedAdjoint_apply, map_one, Matrix.mul_one, Matrix.one_mul, sub_self]
  rw [peirce_graded_adjoint projection projection_isStarProjection charge charge_odd] at hc
  change chargeᴴ * 1 + θ 1 * chargeᴴ = 0 at hc
  rw [map_one, Matrix.one_mul, Matrix.mul_one] at hc
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) hc
  norm_num [charge, conjTranspose_apply] at h00

theorem inner_curvature_negative_energy :
    RCLike.re (inner ℂ probe (D gram probe)) = -32 := by
  rw [hs_inner_eq_trace]
  change RCLike.re (Matrix.trace ((gram * probe - probe * gram) * probeᴴ)) = -32
  norm_num [gram, charge, probe, Matrix.single, Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    conjTranspose_apply, map_ofNat, Fin.sum_univ_succ]

theorem inner_curvature_not_positive : ¬(D gram).IsPositive := by
  intro h
  have hc := h.re_inner_nonneg_right probe
  rw [inner_curvature_negative_energy] at hc
  norm_num at hc

theorem jordan_hodge_positive_energy :
    RCLike.re (inner ℂ probe (J gram probe)) = 56 := by
  rw [hs_inner_eq_trace]
  change RCLike.re (Matrix.trace ((gram * probe + probe * gram) * probeᴴ)) = 56
  norm_num [gram, charge, probe, Matrix.single, Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    conjTranspose_apply, map_ofNat, Fin.sum_univ_succ]

theorem identity_not_hodge_kernel :
    (1 : Matrix (Fin 4) (Fin 4) ℂ) ∉
      (gradedAdjoint θ charge * (gradedAdjoint θ charge).adjoint +
        (gradedAdjoint θ charge).adjoint * gradedAdjoint θ charge).ker := by
  rw [peirce_graded_hodge projection projection_isStarProjection charge charge_odd]
  intro h
  have hc : gram + gram = 0 := by
    simpa only [LinearMap.mem_ker, jordanLeft, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.mul_one, Matrix.one_mul, gram] using h
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) hc
  change gram 0 0 + gram 0 0 = 0 at h00
  rw [gram_entry] at h00
  norm_num at h00

end InfoGeometry.OperatorAlgebra.PeirceSuperoperators.Examples
