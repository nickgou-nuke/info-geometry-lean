/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Ring.Invertible
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel

/-!
# Noncommutative unitriangular matrices and the exact quadratic BCH law

The three coordinates below are entries in an arbitrary associative ring.
`Unitriangular3` has its matrix multiplication law and a faithful representation
by units in `Matrix (Fin 3) (Fin 3) A`. When `2` is invertible, `BCH3` has the
class-two Baker--Campbell--Hausdorff multiplication, and `expEquiv` is an actual
group isomorphism. The associated matrix is exactly `1 + X + (1/2) X^2`.

No commutativity of the coefficient ring is assumed. This is polynomial
nilpotent algebra, with no analytic exponential or convergence assertion.
-/

namespace InfoGeometry.Algebra.UnitriangularBCH3

variable {A : Type*} [Ring A]

abbrev Mat3 (A : Type*) := Matrix (Fin 3) (Fin 3) A

/-- The three strictly upper triangular entries, with the unitriangular
multiplication specified below. -/
@[ext] structure Unitriangular3 (A : Type*) where
  a : A
  b : A
  c : A

namespace Unitriangular3

instance : Group (Unitriangular3 A) where
  mul x y := ⟨x.a + y.a, x.b + y.b, x.c + y.c + x.a * y.b⟩
  one := ⟨0, 0, 0⟩
  inv x := ⟨-x.a, -x.b, -x.c + x.a * x.b⟩
  mul_assoc x y z := by
    apply Unitriangular3.ext
    · change (x.a + y.a) + z.a = x.a + (y.a + z.a)
      exact add_assoc _ _ _
    · change (x.b + y.b) + z.b = x.b + (y.b + z.b)
      exact add_assoc _ _ _
    · change (x.c + y.c + x.a * y.b) + z.c + (x.a + y.a) * z.b =
        x.c + (y.c + z.c + y.a * z.b) + x.a * (y.b + z.b)
      noncomm_ring
  one_mul x := by
    apply Unitriangular3.ext
    · change 0 + x.a = x.a
      exact zero_add _
    · change 0 + x.b = x.b
      exact zero_add _
    · change 0 + x.c + 0 * x.b = x.c
      simp
  mul_one x := by
    apply Unitriangular3.ext
    · change x.a + 0 = x.a
      exact add_zero _
    · change x.b + 0 = x.b
      exact add_zero _
    · change x.c + 0 + x.a * 0 = x.c
      simp
  inv_mul_cancel x := by
    apply Unitriangular3.ext
    · change -x.a + x.a = 0
      exact neg_add_cancel _
    · change -x.b + x.b = 0
      exact neg_add_cancel _
    · change (-x.c + x.a * x.b) + x.c + (-x.a) * x.b = 0
      noncomm_ring

@[simp] theorem mul_a (x y : Unitriangular3 A) : (x * y).a = x.a + y.a := rfl
@[simp] theorem mul_b (x y : Unitriangular3 A) : (x * y).b = x.b + y.b := rfl
@[simp] theorem mul_c (x y : Unitriangular3 A) :
    (x * y).c = x.c + y.c + x.a * y.b := rfl
@[simp] theorem one_a : (1 : Unitriangular3 A).a = 0 := rfl
@[simp] theorem one_b : (1 : Unitriangular3 A).b = 0 := rfl
@[simp] theorem one_c : (1 : Unitriangular3 A).c = 0 := rfl
@[simp] theorem inv_a (x : Unitriangular3 A) : (x⁻¹).a = -x.a := rfl
@[simp] theorem inv_b (x : Unitriangular3 A) : (x⁻¹).b = -x.b := rfl
@[simp] theorem inv_c (x : Unitriangular3 A) : (x⁻¹).c = -x.c + x.a * x.b := rfl

/-- The genuine upper unitriangular matrix with these entries. -/
def toMatrix (x : Unitriangular3 A) : Mat3 A :=
  !![1, x.a, x.c; 0, 1, x.b; 0, 0, 1]

@[simp] theorem toMatrix_one : toMatrix (1 : Unitriangular3 A) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix]

theorem toMatrix_mul (x y : Unitriangular3 A) :
    toMatrix (x * y) = toMatrix x * toMatrix y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;> abel

theorem toMatrix_injective : Function.Injective (toMatrix (A := A)) := by
  intro x y h
  have ha := congrArg (fun M : Mat3 A => M 0 1) h
  have hb := congrArg (fun M : Mat3 A => M 1 2) h
  have hc := congrArg (fun M : Mat3 A => M 0 2) h
  exact Unitriangular3.ext ha hb hc

/-- A faithful representation by actual invertible matrices. -/
def toUnits : Unitriangular3 A →* (Mat3 A)ˣ where
  toFun x :=
    { val := toMatrix x
      inv := toMatrix x⁻¹
      val_inv := by rw [← toMatrix_mul, mul_inv_cancel, toMatrix_one]
      inv_val := by rw [← toMatrix_mul, inv_mul_cancel, toMatrix_one] }
  map_one' := by
    apply Units.ext
    exact toMatrix_one
  map_mul' x y := by
    apply Units.ext
    exact toMatrix_mul x y

@[simp] theorem coe_toUnits (x : Unitriangular3 A) :
    (toUnits x : Mat3 A) = toMatrix x := rfl

theorem toUnits_injective : Function.Injective (toUnits (A := A)) := by
  intro x y h
  apply toMatrix_injective
  exact congrArg (fun U : (Mat3 A)ˣ => (U : Mat3 A)) h

/-- The unitriangular subgroup inside the units of the full matrix ring. -/
def matrixSubgroup (A : Type*) [Ring A] : Subgroup (Mat3 A)ˣ :=
  (toUnits (A := A)).range

/-- This range is exactly all upper unitriangular matrices, not a selected
subgroup of a larger unipotent carrier. -/
theorem mem_matrixSubgroup_iff (U : (Mat3 A)ˣ) :
    U ∈ matrixSubgroup A ↔
      (U : Mat3 A) 0 0 = 1 ∧ (U : Mat3 A) 1 0 = 0 ∧
      (U : Mat3 A) 1 1 = 1 ∧ (U : Mat3 A) 2 0 = 0 ∧
      (U : Mat3 A) 2 1 = 0 ∧ (U : Mat3 A) 2 2 = 1 := by
  constructor
  · rintro ⟨x, rfl⟩
    simp [toUnits, toMatrix]
  · rintro ⟨h00, h10, h11, h20, h21, h22⟩
    refine ⟨⟨(U : Mat3 A) 0 1, (U : Mat3 A) 1 2, (U : Mat3 A) 0 2⟩, ?_⟩
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [toUnits, toMatrix, h00, h10, h11, h20, h21, h22]

/-- Explicit coordinate extraction gives a computable isomorphism onto the
matrix subgroup; its inverse does not choose an existential witness. -/
def matrixEquiv : Unitriangular3 A ≃* matrixSubgroup A where
  toFun x := ⟨toUnits x, ⟨x, rfl⟩⟩
  invFun U := ⟨(U.val : Mat3 A) 0 1, (U.val : Mat3 A) 1 2, (U.val : Mat3 A) 0 2⟩
  left_inv x := by cases x; rfl
  right_inv U := by
    rcases U with ⟨U, x, rfl⟩
    rfl
  map_mul' x y := by
    apply Subtype.ext
    exact toUnits.map_mul x y

/-- The group commutator is the central upper-right matrix entry. Its
coefficient order is retained even when `A` is noncommutative. -/
theorem group_commutator (x y : Unitriangular3 A) :
    x * y * x⁻¹ * y⁻¹ = ⟨0, 0, x.a * y.b - y.a * x.b⟩ := by
  apply Unitriangular3.ext
  · simp only [mul_a, inv_a]
    abel
  · simp only [mul_b, inv_b]
    abel
  · simp only [mul_c, mul_a, inv_a, inv_b, inv_c]
    noncomm_ring

theorem center_commutes (c : A) (x : Unitriangular3 A) :
    Commute (⟨0, 0, c⟩ : Unitriangular3 A) x := by
  change (⟨0, 0, c⟩ : Unitriangular3 A) * x = x * ⟨0, 0, c⟩
  ext <;> simp [add_comm]

/-- Noncommutation is precisely the ordered cocycle defect, without imposing
any commutation hypothesis on the ring coefficients. -/
theorem commute_iff (x y : Unitriangular3 A) :
    Commute x y ↔ x.a * y.b = y.a * x.b := by
  constructor
  · intro h
    have hc := congrArg Unitriangular3.c h.eq
    simp only [mul_c] at hc
    rw [add_comm y.c x.c] at hc
    exact add_left_cancel hc
  · intro h
    change x * y = y * x
    ext <;> simp [h, add_comm]

/-- Every nonzero coefficient ring supplies noncommuting unitriangular matrices. -/
theorem noncommuting_generators [Nontrivial A] :
    ¬ Commute (⟨1, 0, 0⟩ : Unitriangular3 A) ⟨0, 1, 0⟩ := by
  intro h
  have hc := (commute_iff (⟨1, 0, 0⟩ : Unitriangular3 A) ⟨0, 1, 0⟩).mp h
  simp at hc

/-- Unit translation in the first upper diagonal direction. -/
def firstGenerator : Mat3 A := toMatrix ⟨1, 0, 0⟩

/-- Unit translation in the second upper diagonal direction. -/
def secondGenerator : Mat3 A := toMatrix ⟨0, 1, 0⟩

/-- The faithful matrix realization retains the nonzero ordered product defect. -/
theorem matrix_generators_noncommute [Nontrivial A] :
    (firstGenerator : Mat3 A) * secondGenerator ≠ secondGenerator * firstGenerator := by
  intro h
  apply noncommuting_generators (A := A)
  change (⟨1, 0, 0⟩ : Unitriangular3 A) * ⟨0, 1, 0⟩ =
    (⟨0, 1, 0⟩ : Unitriangular3 A) * ⟨1, 0, 0⟩
  apply toMatrix_injective
  simpa only [toMatrix_mul, firstGenerator, secondGenerator] using h

end Unitriangular3

/-- Logarithmic coordinates on the strict upper triangular matrix algebra.
The multiplication below is BCH, rather than vector addition. -/
@[ext] structure BCH3 (A : Type*) where
  a : A
  b : A
  c : A

namespace BCH3

variable [Invertible (2 : A)]

instance : Group (BCH3 A) where
  mul x y := ⟨x.a + y.a, x.b + y.b,
    x.c + y.c + ⅟(2 : A) * (x.a * y.b - y.a * x.b)⟩
  one := ⟨0, 0, 0⟩
  inv x := ⟨-x.a, -x.b, -x.c⟩
  mul_assoc x y z := by
    apply BCH3.ext
    · change (x.a + y.a) + z.a = x.a + (y.a + z.a)
      exact add_assoc _ _ _
    · change (x.b + y.b) + z.b = x.b + (y.b + z.b)
      exact add_assoc _ _ _
    · change (x.c + y.c + ⅟(2 : A) * (x.a * y.b - y.a * x.b)) + z.c +
          ⅟(2 : A) * ((x.a + y.a) * z.b - z.a * (x.b + y.b)) =
        x.c + (y.c + z.c + ⅟(2 : A) * (y.a * z.b - z.a * y.b)) +
          ⅟(2 : A) * (x.a * (y.b + z.b) - (y.a + z.a) * x.b)
      noncomm_ring
  one_mul x := by
    apply BCH3.ext
    · change 0 + x.a = x.a
      exact zero_add _
    · change 0 + x.b = x.b
      exact zero_add _
    · change 0 + x.c + ⅟(2 : A) * (0 * x.b - x.a * 0) = x.c
      simp
  mul_one x := by
    apply BCH3.ext
    · change x.a + 0 = x.a
      exact add_zero _
    · change x.b + 0 = x.b
      exact add_zero _
    · change x.c + 0 + ⅟(2 : A) * (x.a * 0 - 0 * x.b) = x.c
      simp
  inv_mul_cancel x := by
    apply BCH3.ext
    · change -x.a + x.a = 0
      exact neg_add_cancel _
    · change -x.b + x.b = 0
      exact neg_add_cancel _
    · change -x.c + x.c + ⅟(2 : A) * ((-x.a) * x.b - x.a * (-x.b)) = 0
      simp

@[simp] theorem mul_a (x y : BCH3 A) : (x * y).a = x.a + y.a := rfl
@[simp] theorem mul_b (x y : BCH3 A) : (x * y).b = x.b + y.b := rfl
@[simp] theorem mul_c (x y : BCH3 A) :
    (x * y).c = x.c + y.c + ⅟(2 : A) * (x.a * y.b - y.a * x.b) := rfl
@[simp] theorem one_a : (1 : BCH3 A).a = 0 := rfl
@[simp] theorem one_b : (1 : BCH3 A).b = 0 := rfl
@[simp] theorem one_c : (1 : BCH3 A).c = 0 := rfl
@[simp] theorem inv_a (x : BCH3 A) : (x⁻¹).a = -x.a := rfl
@[simp] theorem inv_b (x : BCH3 A) : (x⁻¹).b = -x.b := rfl
@[simp] theorem inv_c (x : BCH3 A) : (x⁻¹).c = -x.c := rfl

private theorem half_double_mul (z : A) :
    ⅟(2 : A) * z + ⅟(2 : A) * z = z := by
  rw [← add_mul, invOf_two_add_invOf_two, one_mul]

/-- Quadratic exponential and logarithm, as a native multiplicative equivalence. -/
def expEquiv : BCH3 A ≃* Unitriangular3 A where
  toFun x := ⟨x.a, x.b, x.c + ⅟(2 : A) * (x.a * x.b)⟩
  invFun u := ⟨u.a, u.b, u.c - ⅟(2 : A) * (u.a * u.b)⟩
  left_inv x := by
    cases x
    ext <;> simp
  right_inv x := by
    cases x
    ext <;> simp
  map_mul' x y := by
    apply Unitriangular3.ext
    · rfl
    · rfl
    · change
        x.c + y.c + ⅟(2 : A) * (x.a * y.b - y.a * x.b) +
          ⅟(2 : A) * ((x.a + y.a) * (x.b + y.b)) =
        (x.c + ⅟(2 : A) * (x.a * x.b)) +
          (y.c + ⅟(2 : A) * (y.a * y.b)) + x.a * y.b
      calc
        _ = (x.c + ⅟(2 : A) * (x.a * x.b)) +
              (y.c + ⅟(2 : A) * (y.a * y.b)) +
              (⅟(2 : A) * (x.a * y.b) + ⅟(2 : A) * (x.a * y.b)) := by
          noncomm_ring
        _ = _ := by rw [half_double_mul]

/-- The polynomial exponential is a group isomorphism onto a concrete matrix
subgroup, not only a law on unbundled expressions. -/
def matrixExpEquiv : BCH3 A ≃* Unitriangular3.matrixSubgroup A :=
  expEquiv.trans Unitriangular3.matrixEquiv

/-- The strictly upper triangular matrix represented by logarithmic coordinates. -/
def toNilpotent (x : BCH3 A) : Mat3 A :=
  !![0, x.a, x.c; 0, 0, x.b; 0, 0, 0]

omit [Invertible (2 : A)] in
theorem toNilpotent_injective : Function.Injective (toNilpotent (A := A)) := by
  intro x y h
  exact BCH3.ext (congrArg (fun M : Mat3 A => M 0 1) h)
    (congrArg (fun M : Mat3 A => M 1 2) h)
    (congrArg (fun M : Mat3 A => M 0 2) h)

omit [Invertible (2 : A)] in
/-- The logarithmic coordinates cover the entire strictly upper triangular
matrix algebra. -/
theorem exists_toNilpotent_iff (M : Mat3 A) :
    (∃ x : BCH3 A, toNilpotent x = M) ↔
      M 0 0 = 0 ∧ M 1 0 = 0 ∧ M 1 1 = 0 ∧
      M 2 0 = 0 ∧ M 2 1 = 0 ∧ M 2 2 = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    simp [toNilpotent]
  · rintro ⟨h00, h10, h11, h20, h21, h22⟩
    refine ⟨⟨M 0 1, M 1 2, M 0 2⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [toNilpotent, h00, h10, h11, h20, h21, h22]

omit [Invertible (2 : A)] in
theorem toNilpotent_cube (x : BCH3 A) : toNilpotent x ^ 3 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toNilpotent, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

omit [Invertible (2 : A)] in
/-- Algebra-wide nilpotency: every ordered product of three elements vanishes.
This is stronger than the elementwise assertion `X^3 = 0`. -/
theorem toNilpotent_triple_mul_zero (x y z : BCH3 A) :
    (toNilpotent x * toNilpotent y) * toNilpotent z = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toNilpotent, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The exact matrix BCH operation preserves strict upper triangularity. -/
theorem toNilpotent_mul (x y : BCH3 A) :
    toNilpotent (x * y) = toNilpotent x + toNilpotent y +
      ⅟(2 : A) • (toNilpotent x * toNilpotent y - toNilpotent y * toNilpotent x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toNilpotent, smul_eq_mul]

/-- The associated unipotent matrix is the actual quadratic exponential. -/
theorem toMatrix_expEquiv (x : BCH3 A) :
    Unitriangular3.toMatrix (expEquiv x) =
      1 + toNilpotent x + ⅟(2 : A) • (toNilpotent x ^ 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Unitriangular3.toMatrix, expEquiv, toNilpotent, pow_two,
      smul_eq_mul]

/-- The inverse map is the quadratic matrix logarithm. -/
theorem toNilpotent_log (u : Unitriangular3 A) :
    toNilpotent (expEquiv.symm u) =
      (Unitriangular3.toMatrix u - 1) -
        ⅟(2 : A) • ((Unitriangular3.toMatrix u - 1) ^ 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Unitriangular3.toMatrix, expEquiv, toNilpotent, pow_two,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ, smul_eq_mul]

/-- Exact multiplication of the quadratic matrix exponential. -/
theorem quadratic_exp_mul (x y : BCH3 A) :
    (1 + toNilpotent x + ⅟(2 : A) • (toNilpotent x ^ 2)) *
      (1 + toNilpotent y + ⅟(2 : A) • (toNilpotent y ^ 2)) =
    1 + toNilpotent (x * y) + ⅟(2 : A) • (toNilpotent (x * y) ^ 2) := by
  rw [← toMatrix_expEquiv, ← toMatrix_expEquiv, ← toMatrix_expEquiv,
    ← Unitriangular3.toMatrix_mul, expEquiv.map_mul]

/-- Inversion is negation of the logarithmic matrix. -/
theorem toNilpotent_inv (x : BCH3 A) : toNilpotent x⁻¹ = -toNilpotent x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toNilpotent]

/-- Inverse quadratic exponentials multiply to the identity. -/
theorem quadratic_exp_mul_neg (x : BCH3 A) :
    (1 + toNilpotent x + ⅟(2 : A) • (toNilpotent x ^ 2)) *
      (1 - toNilpotent x + ⅟(2 : A) • ((-toNilpotent x) ^ 2)) = 1 := by
  simp only [sub_eq_add_neg, ← toNilpotent_inv]
  rw [quadratic_exp_mul, mul_inv_cancel]
  have hzero : toNilpotent (1 : BCH3 A) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [toNilpotent]
  simp [hzero]

/-- The group-commutator curvature identity in the actual matrix ring. -/
theorem matrix_group_commutator (x y : BCH3 A) :
    Unitriangular3.toMatrix (expEquiv x) *
      Unitriangular3.toMatrix (expEquiv y) *
      Unitriangular3.toMatrix ((expEquiv x)⁻¹) *
      Unitriangular3.toMatrix ((expEquiv y)⁻¹) =
    1 + (toNilpotent x * toNilpotent y - toNilpotent y * toNilpotent x) := by
  rw [← Unitriangular3.toMatrix_mul, ← Unitriangular3.toMatrix_mul,
    ← Unitriangular3.toMatrix_mul, Unitriangular3.group_commutator]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Unitriangular3.toMatrix, expEquiv, toNilpotent]

end BCH3

end InfoGeometry.Algebra.UnitriangularBCH3
