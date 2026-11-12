/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.StrictUpper3
import Mathlib.Algebra.Ring.Invertible
import Mathlib.Algebra.Group.TransferInstance

/-!
# Exact BCH coordinates on the noncommutative unitriangular group

The coefficient ring need not commute. The only extra arithmetic hypothesis
is invertibility of two. The exponential and logarithm are inverse quadratic
polynomials on the full strict upper triangular operator algebra. A separate
type synonym carries the BCH group multiplication; the ordinary additive group
is not identified with a noncommutative group.
-/

namespace InfoGeometry.Algebra.StrictUpper3

variable {A : Type*} [Ring A] [Invertible (2 : A)]

/-- Entrywise multiplication by the canonical inverse of two. -/
def half (X : Strict3 A) : Strict3 A :=
  ⟨fun i j => ⅟(2 : A) * (X : Mat3 A) i j, by
    intro i j hji
    simp only [X.property i j hji, mul_zero]⟩

@[simp] theorem half_zero : half (0 : Strict3 A) = 0 := by
  apply Subtype.ext
  ext i j
  change ⅟(2 : A) * 0 = 0
  exact mul_zero _

theorem half_twice (x : A) : (2 : ℤ) • (⅟(2 : A) * x) = x := by
  rw [two_zsmul, ← add_mul, invOf_two_add_invOf_two, one_mul]

/-- The nilpotent part of the quadratic exponential. -/
def expIncrement (X : Strict3 A) : Strict3 A := X + half (X * X)

/-- The finite logarithm of `1 + X`. -/
def logIncrement (X : Strict3 A) : Strict3 A := X - half (X * X)

theorem expIncrement_normal_form (X : Strict3 A) :
    (expIncrement X : Mat3 A) =
      upper ((X : Mat3 A) 0 1) ((X : Mat3 A) 1 2)
        ((X : Mat3 A) 0 2 + ⅟(2 : A) *
          ((X : Mat3 A) 0 1 * (X : Mat3 A) 1 2)) := by
  ext i j
  change (X : Mat3 A) i j + ⅟(2 : A) *
    ((X : Mat3 A) * (X : Mat3 A)) i j = _
  rw [normal_form X]
  fin_cases i <;> fin_cases j <;>
    simp [upper, Matrix.mul_apply, Fin.sum_univ_succ]

theorem logIncrement_normal_form (X : Strict3 A) :
    (logIncrement X : Mat3 A) =
      upper ((X : Mat3 A) 0 1) ((X : Mat3 A) 1 2)
        ((X : Mat3 A) 0 2 - ⅟(2 : A) *
          ((X : Mat3 A) 0 1 * (X : Mat3 A) 1 2)) := by
  ext i j
  change (X : Mat3 A) i j - ⅟(2 : A) *
    ((X : Mat3 A) * (X : Mat3 A)) i j = _
  rw [normal_form X]
  fin_cases i <;> fin_cases j <;>
    simp [upper, Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem log_expIncrement (X : Strict3 A) :
    logIncrement (expIncrement X) = X := by
  apply Subtype.ext
  rw [logIncrement_normal_form, expIncrement_normal_form, normal_form X]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upper]

@[simp] theorem exp_logIncrement (X : Strict3 A) :
    expIncrement (logIncrement X) = X := by
  apply Subtype.ext
  rw [expIncrement_normal_form, logIncrement_normal_form, normal_form X]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upper]

/-- Explicit exponential/logarithm coordinate equivalence. -/
def expLogEquiv : Strict3 A ≃ Strict3 A where
  toFun := expIncrement
  invFun := logIncrement
  left_inv := log_expIncrement
  right_inv := exp_logIncrement

/-- The actual unit `1 + X + X²/2`. -/
def expUnit (X : Strict3 A) : (Mat3 A)ˣ := onePlusUnit (expIncrement X)

theorem expUnit_val (X : Strict3 A) :
    (expUnit X : Mat3 A) =
      1 + (X : Mat3 A) + (half (X * X) : Mat3 A) := by
  change 1 + ((X : Mat3 A) + (half (X * X) : Mat3 A)) = _
  exact (add_assoc _ _ _).symm

/-- The source multiplication in exponential coordinates. -/
def bch (X Y : Strict3 A) : Strict3 A :=
  X + Y + half (X * Y - Y * X)

theorem bch_normal_form (X Y : Strict3 A) :
    (bch X Y : Mat3 A) =
      upper ((X : Mat3 A) 0 1 + (Y : Mat3 A) 0 1)
        ((X : Mat3 A) 1 2 + (Y : Mat3 A) 1 2)
        ((X : Mat3 A) 0 2 + (Y : Mat3 A) 0 2 +
          ⅟(2 : A) * ((X : Mat3 A) 0 1 * (Y : Mat3 A) 1 2 -
            (Y : Mat3 A) 0 1 * (X : Mat3 A) 1 2)) := by
  ext i j
  change (X : Mat3 A) i j + (Y : Mat3 A) i j + ⅟(2 : A) *
    ((X : Mat3 A) * (Y : Mat3 A) - (Y : Mat3 A) * (X : Mat3 A)) i j = _
  rw [normal_form X, normal_form Y]
  fin_cases i <;> fin_cases j <;>
    simp [upper]

/-- Exact BCH multiplication, including the nonzero ordered commutator. -/
theorem expUnit_mul (X Y : Strict3 A) :
    expUnit X * expUnit Y = expUnit (bch X Y) := by
  apply Units.ext
  change (1 + (expIncrement X : Mat3 A)) * (1 + (expIncrement Y : Mat3 A)) =
    1 + (expIncrement (bch X Y) : Mat3 A)
  rw [expIncrement_normal_form, expIncrement_normal_form, expIncrement_normal_form,
    bch_normal_form]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upper, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]
  all_goals (solve | abel | noncomm_ring [half_twice])

@[simp] theorem expUnit_zero : expUnit (0 : Strict3 A) = 1 := by
  apply Units.ext
  rw [expUnit_val]
  simp

theorem bch_neg (X : Strict3 A) : bch X (-X) = 0 := by
  simp [bch]

theorem expUnit_neg (X : Strict3 A) : expUnit (-X) = (expUnit X)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [expUnit_mul, bch_neg, expUnit_zero]

/-- The exact group commutator in exponential coordinates. -/
theorem expUnit_commutator (X Y : Strict3 A) :
    (↑(expUnit X * expUnit Y * (expUnit X)⁻¹ * (expUnit Y)⁻¹) : Mat3 A) =
      1 + ((X : Mat3 A) * (Y : Mat3 A) - (Y : Mat3 A) * (X : Mat3 A)) := by
  rw [expUnit, expUnit, onePlusUnit_commutator]
  rw [expIncrement_normal_form, expIncrement_normal_form, normal_form X, normal_form Y]
  simp only [upper_mul]
  rfl

/-- Exponential/logarithm equivalence onto the full native unitriangular subgroup. -/
def expEquiv : Strict3 A ≃ U3 A := expLogEquiv.trans shiftEquiv

@[simp] theorem expEquiv_unit (X : Strict3 A) :
    (expEquiv X).val = expUnit X := rfl

/-- A separate carrier for BCH multiplication, not the additive group. -/
def BCH (A : Type*) [Ring A] := Strict3 A

/-- Read the underlying strict upper triangular matrix. -/
def toStrict (X : BCH A) : Strict3 A := X

/-- Use a strict upper triangular matrix as BCH coordinates. -/
def ofStrict (X : Strict3 A) : BCH A := X

def bchEquiv : BCH A ≃ U3 A :=
  (show BCH A ≃ Strict3 A from Equiv.refl _).trans expEquiv

instance : Group (BCH A) := bchEquiv.group

/-- The genuine group isomorphism supplied by the quadratic exponential. -/
def expMulEquiv : BCH A ≃* U3 A := bchEquiv.mulEquiv

@[simp] theorem expMulEquiv_unit (X : BCH A) :
    (expMulEquiv X).val = expUnit (toStrict X) := rfl

/-- The transferred multiplication is exactly the displayed BCH polynomial. -/
theorem toStrict_mul (X Y : BCH A) :
    toStrict (X * Y) = bch (toStrict X) (toStrict Y) := by
  apply expEquiv.injective
  apply Subtype.ext
  change (expMulEquiv (X * Y)).val = expUnit (bch (toStrict X) (toStrict Y))
  rw [map_mul]
  exact expUnit_mul (toStrict X) (toStrict Y)

@[simp] theorem toStrict_one : toStrict (1 : BCH A) = 0 := by
  apply expEquiv.injective
  apply Subtype.ext
  change (expMulEquiv (1 : BCH A)).val = expUnit 0
  rw [map_one, expUnit_zero]
  rfl

@[simp] theorem toStrict_inv (X : BCH A) : toStrict X⁻¹ = -toStrict X := by
  apply expEquiv.injective
  apply Subtype.ext
  change (expMulEquiv X⁻¹).val = expUnit (-toStrict X)
  rw [map_inv, expUnit_neg]
  rfl

end InfoGeometry.Algebra.StrictUpper3
