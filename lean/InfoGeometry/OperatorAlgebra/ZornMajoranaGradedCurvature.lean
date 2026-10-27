/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint
import InfoGeometry.Algebra.ZornLeftMajoranaCovariance
import Mathlib.Tactic.NormNum

/-!
# Noncentral graded curvature from native Zorn Majorana operators

The existing left grading acts on the actual Zorn module, and conjugation by
that involution grades its full associative endomorphism algebra. The charge
is a sum of one Majorana operator and a product of three Majorana operators.
Its oddness follows from the actual grading, and its square has a nonzero
commutator with a Majorana generator over the reals.

The cubic product is used as an odd word; no integer grading or Clifford
grade-identification is asserted. All products of operators are native
endomorphism composition, not the nonassociative Zorn product.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ZornMajoranaGradedCurvature

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix
  (diagonal left_diagonal_difference_involution leftMajoranaPlus
    leftMajoranaPlus_odd leftMajoranaPlus_anticommutator
    leftMajoranaPlus_basis_square E11)
open InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint

variable {R : Type*} [CommRing R]

abbrev ZornOp (R : Type*) [CommRing R] := Module.End R (ZornVectorMatrix R)

/-- The existing left grading on the full Zorn module. -/
abbrev leftGrading : ZornOp R :=
  L_map (R := R) (diagonal 1 (-1) : ZornVectorMatrix R)

/-- Bundle the already proved grading involution using the native constructor. -/
def gradingLinearEquiv : ZornVectorMatrix R ≃ₗ[R] ZornVectorMatrix R :=
  LinearEquiv.ofInvolutive (leftGrading (R := R)) (by
    intro X
    exact congrArg (fun T : ZornOp R => T X)
      (left_diagonal_difference_involution (R := R)))

/-- Actual algebra parity on all endomorphisms, given by grading conjugation. -/
def operatorParity : ZornOp R ≃ₐ[R] ZornOp R :=
  (gradingLinearEquiv (R := R)).conjAlgEquiv R

@[simp] theorem operatorParity_apply (T : ZornOp R) :
    operatorParity T = leftGrading * T * leftGrading := by
  apply LinearMap.ext
  intro X
  rfl

theorem operatorParity_involutive :
    Function.Involutive (operatorParity (R := R)) := by
  intro T
  have hΓ : (leftGrading : ZornOp R) * leftGrading = 1 :=
    left_diagonal_difference_involution
  rw [operatorParity_apply, operatorParity_apply]
  calc
    leftGrading * (leftGrading * T * leftGrading) * leftGrading =
        (leftGrading * leftGrading) * T * (leftGrading * leftGrading) := by
      noncomm_ring
    _ = T := by simp only [hΓ, one_mul, mul_one]

/-- The positive modes are the existing native Majorana operators. -/
abbrev positiveMode (i : Fin 3) : ZornOp R :=
  leftMajoranaPlus (ZornVec3.basis (R := R) i)

theorem positiveMode_odd (i : Fin 3) :
    operatorParity (positiveMode (R := R) i) = -positiveMode i := by
  have hΓ : (leftGrading : ZornOp R) * leftGrading = 1 :=
    left_diagonal_difference_involution
  have hanti : leftGrading * positiveMode (R := R) i =
      -(positiveMode i * leftGrading) :=
    eq_neg_of_add_eq_zero_left (leftMajoranaPlus_odd (ZornVec3.basis i))
  rw [operatorParity_apply, hanti]
  simp only [neg_mul, mul_assoc, hΓ, mul_one]

/-- Distinct modes anticommute by the native polarized Majorana relation. -/
theorem positiveMode_anticommutes (i j : Fin 3) (hij : i ≠ j) :
    positiveMode (R := R) i * positiveMode j =
      -(positiveMode j * positiveMode i) := by
  apply eq_neg_of_add_eq_zero_left
  simpa only [positiveMode, ZornVec3.dot_basis_basis, ite_eq_right hij,
    mul_zero, zero_smul] using
    leftMajoranaPlus_anticommutator
      (ZornVec3.basis (R := R) i) (ZornVec3.basis j)

/-- A genuinely odd charge containing a nontrivial cubic operator word. -/
def higherOddCharge : ZornOp R :=
  positiveMode 0 + positiveMode 0 * positiveMode 1 * positiveMode 2

theorem higherOddCharge_odd :
    operatorParity (higherOddCharge (R := R)) = -higherOddCharge := by
  simp only [higherOddCharge, map_add, map_mul, positiveMode_odd]
  noncomm_ring

/-- Ordered CAR reduction; no ambient commutativity is assumed. -/
private theorem threeModeCharge_square {A : Type*} [Ring A]
    (a b c : A) (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hba : b * a = -(a * b)) (hca : c * a = -(a * c))
    (hcb : c * b = -(b * c)) :
    (a + a * b * c) * (a + a * b * c) = 2 * (b * c) := by
  have hbc : (b * c) * (b * c) = -1 := by
    calc
      (b * c) * (b * c) = b * (c * b) * c := by noncomm_ring
      _ = b * (-(b * c)) * c := by rw [hcb]
      _ = -((b * b) * (c * c)) := by noncomm_ring
      _ = -1 := by rw [hb, hc, one_mul]
  have hbca : (b * c) * a = a * (b * c) := by
    calc
      (b * c) * a = b * (c * a) := mul_assoc _ _ _
      _ = b * (-(a * c)) := by rw [hca]
      _ = -(b * a) * c := by noncomm_ring
      _ = a * (b * c) := by rw [hba]; noncomm_ring
  have hleft : a * (a * (b * c)) = b * c := by
    rw [← mul_assoc, ha, one_mul]
  have hright : (a * (b * c)) * a = b * c := by
    rw [mul_assoc, hbca, hleft]
  have hword : (a * (b * c)) * (a * (b * c)) = -1 := by
    calc
      (a * (b * c)) * (a * (b * c)) =
          a * ((b * c) * a) * (b * c) := by noncomm_ring
      _ = a * (a * (b * c)) * (b * c) := by rw [hbca]
      _ = (b * c) * (b * c) := by rw [hleft]
      _ = -1 := hbc
  calc
    (a + a * b * c) * (a + a * b * c) =
        a * a + a * (a * (b * c)) + (a * (b * c)) * a +
          (a * (b * c)) * (a * (b * c)) := by noncomm_ring
    _ = 1 + b * c + b * c + (-1) := by rw [ha, hleft, hright, hword]
    _ = 2 * (b * c) := by noncomm_ring

/-- The scalar terms cancel, leaving a nontrivial even operator product. -/
theorem higherOddCharge_square :
    higherOddCharge (R := R) * higherOddCharge =
      (2 : R) • (positiveMode 1 * positiveMode 2) := by
  have h := threeModeCharge_square
    (positiveMode (R := R) 0) (positiveMode 1) (positiveMode 2)
    (leftMajoranaPlus_basis_square (R := R) 0)
    (leftMajoranaPlus_basis_square (R := R) 1)
    (leftMajoranaPlus_basis_square (R := R) 2)
    (positiveMode_anticommutes (R := R) 1 0 (by decide))
    (positiveMode_anticommutes (R := R) 2 0 (by decide))
    (positiveMode_anticommutes (R := R) 2 1 (by decide))
  simpa only [higherOddCharge, Algebra.smul_def, map_ofNat] using h

/-- An exact noncommutative curvature action on a native Majorana generator. -/
theorem higherOddCharge_square_commutator :
    (higherOddCharge (R := R) * higherOddCharge) * positiveMode 1 -
      positiveMode 1 * (higherOddCharge * higherOddCharge) =
        (-4 : R) • positiveMode 2 := by
  have hb : positiveMode (R := R) 1 * positiveMode 1 = 1 :=
    leftMajoranaPlus_basis_square 1
  have hcb := positiveMode_anticommutes (R := R) 2 1 (by decide)
  have hleft : (positiveMode (R := R) 1 * positiveMode 2) * positiveMode 1 =
      -positiveMode 2 := by
    rw [mul_assoc, hcb, mul_neg, ← mul_assoc, hb, one_mul]
  have hright : positiveMode (R := R) 1 * (positiveMode 1 * positiveMode 2) =
      positiveMode 2 := by
    rw [← mul_assoc, hb, one_mul]
  calc
    (higherOddCharge (R := R) * higherOddCharge) * positiveMode 1 -
        positiveMode 1 * (higherOddCharge * higherOddCharge) =
      (2 : ZornOp R) * ((positiveMode 1 * positiveMode 2) * positiveMode 1 -
        positiveMode 1 * (positiveMode 1 * positiveMode 2)) := by
      simp only [higherOddCharge_square, Algebra.smul_def, map_ofNat]
      noncomm_ring
    _ = (2 : ZornOp R) * (-positiveMode 2 - positiveMode 2) := by
      rw [hleft, hright]
    _ = (-4 : R) • positiveMode 2 := by
      simp only [Algebra.smul_def, map_neg, map_ofNat]
      noncomm_ring

/-- The associated native endomorphism of the entire Zorn operator algebra. -/
def chargeDifferential : Module.End R (ZornOp R) :=
  gradedAdjoint operatorParity higherOddCharge

theorem chargeDifferential_square_on_mode_one :
    chargeDifferential (R := R) (chargeDifferential (positiveMode 1)) =
      (-4 : R) • positiveMode 2 := by
  change gradedAdjoint operatorParity higherOddCharge
    (gradedAdjoint operatorParity higherOddCharge (positiveMode 1)) = _
  rw [gradedAdjoint_square_apply operatorParity operatorParity_involutive
    higherOddCharge higherOddCharge_odd]
  exact higherOddCharge_square_commutator

/-- Nonvanishing is witnessed on the native module; no faithfulness axiom is added. -/
theorem positiveMode_two_ne_zero : positiveMode (R := ℝ) 2 ≠ 0 := by
  intro h
  have hs : positiveMode (R := ℝ) 2 * positiveMode 2 = (1 : ZornOp ℝ) :=
    leftMajoranaPlus_basis_square 2
  rw [h, zero_mul] at hs
  have hcoord := congrArg (fun T : ZornOp ℝ => (T E11).a) hs
  simp [E11] at hcoord

theorem curvature_mode_two_ne_zero :
    (-4 : ℝ) • positiveMode (R := ℝ) 2 ≠ 0 := by
  exact smul_ne_zero (by norm_num) positiveMode_two_ne_zero

theorem chargeDifferential_square_on_mode_one_ne_zero :
    chargeDifferential (R := ℝ) (chargeDifferential (positiveMode 1)) ≠ 0 := by
  rw [chargeDifferential_square_on_mode_one]
  exact curvature_mode_two_ne_zero

/-- The squared endomorphism is genuinely nonzero on the full coefficient algebra. -/
theorem chargeDifferential_square_ne_zero :
    chargeDifferential (R := ℝ) * chargeDifferential ≠ 0 := by
  intro h
  have hX := congrArg
    (fun D : Module.End ℝ (ZornOp ℝ) => D (positiveMode (R := ℝ) 1)) h
  change chargeDifferential (chargeDifferential (positiveMode (R := ℝ) 1)) = 0 at hX
  exact chargeDifferential_square_on_mode_one_ne_zero hX

/-- Evenness of a square does not imply that it is central. -/
theorem higherOddCharge_square_not_central :
    ¬ ∀ T : ZornOp ℝ,
      Commute (higherOddCharge (R := ℝ) * higherOddCharge) T := by
  intro h
  apply chargeDifferential_square_ne_zero
  exact (gradedAdjoint_square_eq_zero_iff operatorParity operatorParity_involutive
    higherOddCharge higherOddCharge_odd).mpr h

end InfoGeometry.OperatorAlgebra.ZornMajoranaGradedCurvature
