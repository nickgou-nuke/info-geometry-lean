/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Ring.Invertible
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing

/-!
# Exact cubic-nilpotent BCH over noncommutative coefficients

`Unitriangular3 A` carries the multiplication of all upper-unitriangular 3 by 3
matrices over the arbitrary coefficient ring `A`. Its faithful homomorphism
lands in the unit group of the matrix ring; its range is an actual `Subgroup`.

`BCH3 A` is the three-coordinate model of all strictly upper-triangular
matrices. When `2 : A` is invertible, its group multiplication is
`X + Y + (1/2)[X,Y]`. The quadratic exponential is a `MulEquiv` onto the
upper-unitriangular subgroup. Coefficient products are never commuted.

The half hypothesis is confined to the BCH/exponential section. The integral
unitriangular group and its group-commutator formula need only `[Ring A]`.
No analytic exponential or topological Lie group is asserted.
-/

namespace InfoGeometry.Algebra.UnitriangularBCH

open Matrix

variable {A : Type*} [Ring A]

/-- Coordinates `(01,12,02)` for the full upper-unitriangular matrix group. -/
@[ext] structure Unitriangular3 (A : Type*) where
  a : A
  b : A
  c : A

instance unitriangular3Group : Group (Unitriangular3 A) where
  one := ⟨0, 0, 0⟩
  mul x y := ⟨x.a + y.a, x.b + y.b, x.c + y.c + x.a * y.b⟩
  inv x := ⟨-x.a, -x.b, -x.c + x.a * x.b⟩
  mul_assoc x y z := by
    apply Unitriangular3.ext
    · exact add_assoc x.a y.a z.a
    · exact add_assoc x.b y.b z.b
    · change (x.c + y.c + x.a * y.b) + z.c + (x.a + y.a) * z.b =
        x.c + (y.c + z.c + y.a * z.b) + x.a * (y.b + z.b)
      noncomm_ring
  one_mul x := by
    apply Unitriangular3.ext
    · exact zero_add x.a
    · exact zero_add x.b
    · change 0 + x.c + 0 * x.b = x.c
      simp
  mul_one x := by
    apply Unitriangular3.ext
    · exact add_zero x.a
    · exact add_zero x.b
    · change x.c + 0 + x.a * 0 = x.c
      simp
  inv_mul_cancel x := by
    apply Unitriangular3.ext
    · exact neg_add_cancel x.a
    · exact neg_add_cancel x.b
    · change (-x.c + x.a * x.b) + x.c + (-x.a) * x.b = 0
      noncomm_ring

@[simp] theorem unitriangular_mul_a (x y : Unitriangular3 A) :
    (x * y).a = x.a + y.a := rfl
@[simp] theorem unitriangular_mul_b (x y : Unitriangular3 A) :
    (x * y).b = x.b + y.b := rfl
@[simp] theorem unitriangular_mul_c (x y : Unitriangular3 A) :
    (x * y).c = x.c + y.c + x.a * y.b := rfl

@[simp] theorem unitriangular_one_a : (1 : Unitriangular3 A).a = 0 := rfl
@[simp] theorem unitriangular_one_b : (1 : Unitriangular3 A).b = 0 := rfl
@[simp] theorem unitriangular_one_c : (1 : Unitriangular3 A).c = 0 := rfl

@[simp] theorem unitriangular_inv_a (x : Unitriangular3 A) : x⁻¹.a = -x.a := rfl
@[simp] theorem unitriangular_inv_b (x : Unitriangular3 A) : x⁻¹.b = -x.b := rfl
@[simp] theorem unitriangular_inv_c (x : Unitriangular3 A) :
    x⁻¹.c = -x.c + x.a * x.b := rfl

/-- The genuine noncommutative matrix represented by the coordinates. -/
def toMatrix (x : Unitriangular3 A) : Matrix (Fin 3) (Fin 3) A :=
  !![1, x.a, x.c; 0, 1, x.b; 0, 0, 1]

@[simp] theorem toMatrix_one : toMatrix (1 : Unitriangular3 A) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix]

@[simp] theorem toMatrix_mul (x y : Unitriangular3 A) :
    toMatrix (x * y) = toMatrix x * toMatrix y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, Matrix.mul_apply, Fin.sum_univ_three,
      add_assoc, add_comm]

theorem toMatrix_injective : Function.Injective (toMatrix (A := A)) := by
  intro x y h
  apply Unitriangular3.ext
  · exact congrArg (fun M : Matrix (Fin 3) (Fin 3) A => M 0 1) h
  · exact congrArg (fun M : Matrix (Fin 3) (Fin 3) A => M 1 2) h
  · exact congrArg (fun M : Matrix (Fin 3) (Fin 3) A => M 0 2) h

/-- The coordinate group embeds in the unit group of the full matrix ring. -/
def matrixUnit (x : Unitriangular3 A) : (Matrix (Fin 3) (Fin 3) A)ˣ where
  val := toMatrix x
  inv := toMatrix x⁻¹
  val_inv := by rw [← toMatrix_mul, mul_inv_cancel, toMatrix_one]
  inv_val := by rw [← toMatrix_mul, inv_mul_cancel, toMatrix_one]

def matrixUnitHom : Unitriangular3 A →* (Matrix (Fin 3) (Fin 3) A)ˣ where
  toFun := matrixUnit
  map_one' := by apply Units.ext; exact toMatrix_one
  map_mul' x y := by apply Units.ext; exact toMatrix_mul x y

theorem matrixUnitHom_injective : Function.Injective (matrixUnitHom (A := A)) := by
  intro x y h
  exact toMatrix_injective (congrArg Units.val h)

/-- The full upper-unitriangular subgroup, realized inside the matrix unit group. -/
def unipotentSubgroup : Subgroup (Matrix (Fin 3) (Fin 3) A)ˣ := matrixUnitHom.range

/-- The coordinate representation is faithful and surjective onto its actual subgroup. -/
noncomputable def unitriangularEquivSubgroup :
    Unitriangular3 A ≃* unipotentSubgroup (A := A) :=
  MonoidHom.ofInjective matrixUnitHom_injective

/-- Membership is exactly the displayed upper-unitriangular matrix shape. -/
theorem mem_unipotentSubgroup_iff (u : (Matrix (Fin 3) (Fin 3) A)ˣ) :
    u ∈ unipotentSubgroup (A := A) ↔
      ∃ a b c : A, (u : Matrix (Fin 3) (Fin 3) A) =
        !![1, a, c; 0, 1, b; 0, 0, 1] := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.a, x.b, x.c, rfl⟩
  · rintro ⟨a, b, c, h⟩
    refine ⟨⟨a, b, c⟩, ?_⟩
    apply Units.ext
    exact h.symm

/-- The ordered coefficient defect is the full group commutator. -/
theorem unitriangular_commutator (x y : Unitriangular3 A) :
    x * y * x⁻¹ * y⁻¹ = ⟨0, 0, x.a * y.b - y.a * x.b⟩ := by
  apply Unitriangular3.ext
  · simp only [unitriangular_mul_a, unitriangular_inv_a]
    abel
  · simp only [unitriangular_mul_b, unitriangular_inv_b]
    abel
  · simp only [unitriangular_mul_c, unitriangular_mul_a,
      unitriangular_inv_a, unitriangular_inv_b, unitriangular_inv_c]
    noncomm_ring

/-- Centrality here means within the upper-unitriangular subgroup, not the full matrix ring. -/
theorem central_coordinate_commutes (c : A) (x : Unitriangular3 A) :
    Commute (⟨0, 0, c⟩ : Unitriangular3 A) x := by
  change (⟨0, 0, c⟩ : Unitriangular3 A) * x = x * ⟨0, 0, c⟩
  ext <;> simp [add_comm]

/-- Coordinates of all strictly upper-triangular matrices. The group law below
is BCH multiplication; it is not the ordinary addition of these coordinates. -/
@[ext] structure BCH3 (A : Type*) where
  a : A
  b : A
  c : A

def nilpotentMatrix (x : BCH3 A) : Matrix (Fin 3) (Fin 3) A :=
  !![0, x.a, x.c; 0, 0, x.b; 0, 0, 0]

theorem nilpotentMatrix_injective : Function.Injective (nilpotentMatrix (A := A)) := by
  intro x y h
  apply BCH3.ext
  · exact congrArg (fun M : Matrix (Fin 3) (Fin 3) A => M 0 1) h
  · exact congrArg (fun M : Matrix (Fin 3) (Fin 3) A => M 1 2) h
  · exact congrArg (fun M : Matrix (Fin 3) (Fin 3) A => M 0 2) h

/-- This is exactly all strictly upper-triangular matrices, not a proper family. -/
theorem nilpotentMatrix_range_iff (M : Matrix (Fin 3) (Fin 3) A) :
    (∃ x : BCH3 A, nilpotentMatrix x = M) ↔ ∀ i j, j ≤ i → M i j = 0 := by
  constructor
  · rintro ⟨x, rfl⟩ i j h
    fin_cases i <;> fin_cases j <;> simp_all [nilpotentMatrix]
  · intro h
    refine ⟨⟨M 0 1, M 1 2, M 0 2⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nilpotentMatrix, h]

/-- Every ordered product of three strictly upper-triangular matrices vanishes. -/
theorem nilpotentMatrix_triple (x y z : BCH3 A) :
    nilpotentMatrix x * nilpotentMatrix y * nilpotentMatrix z = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nilpotentMatrix, Matrix.mul_apply, Fin.sum_univ_three]

theorem nilpotentMatrix_cube (x : BCH3 A) : nilpotentMatrix x ^ 3 = 0 := by
  calc
    nilpotentMatrix x ^ 3 = nilpotentMatrix x * nilpotentMatrix x * nilpotentMatrix x := by
      noncomm_ring
    _ = 0 := nilpotentMatrix_triple x x x

/-- The Lie commutator has only its top-right coordinate. -/
theorem nilpotentMatrix_commutator (x y : BCH3 A) :
    nilpotentMatrix x * nilpotentMatrix y - nilpotentMatrix y * nilpotentMatrix x =
      nilpotentMatrix ⟨0, 0, x.a * y.b - y.a * x.b⟩ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nilpotentMatrix]

/-- The first elementary step in the two-step upper-triangular chain. -/
def firstStep : Matrix (Fin 3) (Fin 3) A :=
  nilpotentMatrix (⟨1, 0, 0⟩ : BCH3 A)

/-- The second elementary step in the same chain. -/
def secondStep : Matrix (Fin 3) (Fin 3) A :=
  nilpotentMatrix (⟨0, 1, 0⟩ : BCH3 A)

/-- Square-zero elementary steps fail to commute in every nontrivial coefficient ring. -/
theorem elementary_steps_noncommute [Nontrivial A] :
    firstStep (A := A) * secondStep ≠ secondStep * firstStep := by
  intro h
  have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) A => M 0 2) h
  simp [firstStep, secondStep, nilpotentMatrix, Matrix.mul_apply, Fin.sum_univ_three] at h02

section Half

variable [Invertible (2 : A)]

private theorem half_double_mul (a : A) :
    (⅟ (2 : A)) * a + (⅟ (2 : A)) * a = a := by
  rw [← add_mul, invOf_two_add_invOf_two, one_mul]

instance bch3Group : Group (BCH3 A) where
  one := ⟨0, 0, 0⟩
  mul x y := ⟨x.a + y.a, x.b + y.b,
    x.c + y.c + (⅟ (2 : A)) * (x.a * y.b - y.a * x.b)⟩
  inv x := ⟨-x.a, -x.b, -x.c⟩
  mul_assoc x y z := by
    apply BCH3.ext
    · exact add_assoc x.a y.a z.a
    · exact add_assoc x.b y.b z.b
    · change (x.c + y.c + (⅟ (2 : A)) * (x.a * y.b - y.a * x.b)) + z.c +
          (⅟ (2 : A)) * ((x.a + y.a) * z.b - z.a * (x.b + y.b)) =
        x.c + (y.c + z.c + (⅟ (2 : A)) * (y.a * z.b - z.a * y.b)) +
          (⅟ (2 : A)) * (x.a * (y.b + z.b) - (y.a + z.a) * x.b)
      noncomm_ring
  one_mul x := by
    apply BCH3.ext
    · exact zero_add x.a
    · exact zero_add x.b
    · change 0 + x.c + (⅟ (2 : A)) * (0 * x.b - x.a * 0) = x.c
      simp
  mul_one x := by
    apply BCH3.ext
    · exact add_zero x.a
    · exact add_zero x.b
    · change x.c + 0 + (⅟ (2 : A)) * (x.a * 0 - 0 * x.b) = x.c
      simp
  inv_mul_cancel x := by
    apply BCH3.ext
    · exact neg_add_cancel x.a
    · exact neg_add_cancel x.b
    · change -x.c + x.c + (⅟ (2 : A)) * ((-x.a) * x.b - x.a * (-x.b)) = 0
      noncomm_ring

@[simp] theorem bch_mul_a (x y : BCH3 A) : (x * y).a = x.a + y.a := rfl
@[simp] theorem bch_mul_b (x y : BCH3 A) : (x * y).b = x.b + y.b := rfl
@[simp] theorem bch_mul_c (x y : BCH3 A) :
    (x * y).c = x.c + y.c + (⅟ (2 : A)) * (x.a * y.b - y.a * x.b) := rfl

@[simp] theorem bch_one_a : (1 : BCH3 A).a = 0 := rfl
@[simp] theorem bch_one_b : (1 : BCH3 A).b = 0 := rfl
@[simp] theorem bch_one_c : (1 : BCH3 A).c = 0 := rfl

@[simp] theorem bch_inv_a (x : BCH3 A) : x⁻¹.a = -x.a := rfl
@[simp] theorem bch_inv_b (x : BCH3 A) : x⁻¹.b = -x.b := rfl
@[simp] theorem bch_inv_c (x : BCH3 A) : x⁻¹.c = -x.c := rfl

/-- The quadratic correction from Lie coordinates to matrix-group coordinates. -/
def expCoordinates (x : BCH3 A) : Unitriangular3 A :=
  ⟨x.a, x.b, x.c + (⅟ (2 : A)) * (x.a * x.b)⟩

/-- The inverse quadratic logarithm. -/
def logCoordinates (x : Unitriangular3 A) : BCH3 A :=
  ⟨x.a, x.b, x.c - (⅟ (2 : A)) * (x.a * x.b)⟩

theorem expCoordinates_mul (x y : BCH3 A) :
    expCoordinates (x * y) = expCoordinates x * expCoordinates y := by
  apply Unitriangular3.ext
  · rfl
  · rfl
  · change x.c + y.c + (⅟ (2 : A)) * (x.a * y.b - y.a * x.b) +
        (⅟ (2 : A)) * ((x.a + y.a) * (x.b + y.b)) =
      (x.c + (⅟ (2 : A)) * (x.a * x.b)) +
        (y.c + (⅟ (2 : A)) * (y.a * y.b)) + x.a * y.b
    calc
      _ = (x.c + (⅟ (2 : A)) * (x.a * x.b)) +
          (y.c + (⅟ (2 : A)) * (y.a * y.b)) +
          ((⅟ (2 : A)) * (x.a * y.b) + (⅟ (2 : A)) * (x.a * y.b)) := by
            noncomm_ring
      _ = _ := by rw [half_double_mul]

/-- The genuine BCH group is isomorphic to the full unitriangular group. -/
def expCoordinatesEquiv : BCH3 A ≃* Unitriangular3 A where
  toFun := expCoordinates
  invFun := logCoordinates
  left_inv x := by ext <;> simp [logCoordinates, expCoordinates]
  right_inv x := by ext <;> simp [logCoordinates, expCoordinates]
  map_mul' := expCoordinates_mul

/-- The exponential is a group isomorphism onto the actual matrix subgroup. -/
noncomputable def expEquivSubgroup : BCH3 A ≃* unipotentSubgroup (A := A) :=
  expCoordinatesEquiv.trans unitriangularEquivSubgroup

/-- The exact polynomial exponential. The scalar action is entrywise left multiplication. -/
def exp2 (M : Matrix (Fin 3) (Fin 3) A) : Matrix (Fin 3) (Fin 3) A :=
  1 + M + (⅟ (2 : A)) • (M * M)

/-- The coordinate exponential is exactly `1 + X + (1/2)X²`. -/
theorem expCoordinates_matrix (x : BCH3 A) :
    toMatrix (expCoordinates x) = exp2 (nilpotentMatrix x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, expCoordinates, exp2, nilpotentMatrix, smul_eq_mul]

/-- The BCH group operation realizes the ordered matrix BCH polynomial. -/
theorem bch_matrix (x y : BCH3 A) :
    nilpotentMatrix (x * y) = nilpotentMatrix x + nilpotentMatrix y +
      (⅟ (2 : A)) • (nilpotentMatrix x * nilpotentMatrix y -
        nilpotentMatrix y * nilpotentMatrix x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nilpotentMatrix, smul_eq_mul]

/-- Exact BCH multiplication for noncommuting strictly upper-triangular matrices. -/
theorem exp2_bch (x y : BCH3 A) :
    exp2 (nilpotentMatrix x) * exp2 (nilpotentMatrix y) =
      exp2 (nilpotentMatrix x + nilpotentMatrix y +
        (⅟ (2 : A)) • (nilpotentMatrix x * nilpotentMatrix y -
          nilpotentMatrix y * nilpotentMatrix x)) := by
  rw [← bch_matrix, ← expCoordinates_matrix, ← expCoordinates_matrix,
    ← expCoordinates_matrix, ← toMatrix_mul, ← expCoordinates_mul]

/-- Under the BCH group law the inverse is ordinary negation of the matrix. -/
theorem nilpotentMatrix_inv (x : BCH3 A) : nilpotentMatrix x⁻¹ = -nilpotentMatrix x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nilpotentMatrix]

/-- Both inverse identities come from the genuine BCH group and matrix representation. -/
theorem exp2_mul_exp2_neg (x : BCH3 A) :
    exp2 (nilpotentMatrix x) * exp2 (-nilpotentMatrix x) = 1 := by
  rw [← nilpotentMatrix_inv, ← expCoordinates_matrix, ← expCoordinates_matrix,
    ← toMatrix_mul, ← expCoordinates_mul, mul_inv_cancel]
  have he : expCoordinates (1 : BCH3 A) = 1 :=
    (expCoordinatesEquiv (A := A)).map_one
  rw [he, toMatrix_one]

theorem exp2_neg_mul_exp2 (x : BCH3 A) :
    exp2 (-nilpotentMatrix x) * exp2 (nilpotentMatrix x) = 1 := by
  simpa only [nilpotentMatrix_inv, neg_neg] using exp2_mul_exp2_neg x⁻¹

/-- The polynomial identity on arbitrary matrices with strictly upper support. -/
theorem exp2_bch_of_strict_upper (X Y : Matrix (Fin 3) (Fin 3) A)
    (hX : ∀ i j, j ≤ i → X i j = 0) (hY : ∀ i j, j ≤ i → Y i j = 0) :
    exp2 X * exp2 Y = exp2 (X + Y + (⅟ (2 : A)) • (X * Y - Y * X)) := by
  obtain ⟨x, rfl⟩ := (nilpotentMatrix_range_iff X).2 hX
  obtain ⟨y, rfl⟩ := (nilpotentMatrix_range_iff Y).2 hY
  exact exp2_bch x y

def expUnitHom : BCH3 A →* (Matrix (Fin 3) (Fin 3) A)ˣ :=
  matrixUnitHom.comp expCoordinatesEquiv.toMonoidHom

@[simp] theorem coe_expUnitHom (x : BCH3 A) :
    ((expUnitHom x : (Matrix (Fin 3) (Fin 3) A)ˣ) : Matrix (Fin 3) (Fin 3) A) =
      exp2 (nilpotentMatrix x) := expCoordinates_matrix x

/-- The commutator in the matrix unit group is one plus the algebra commutator. -/
theorem expUnitHom_commutator (x y : BCH3 A) :
    ((expUnitHom x * expUnitHom y * (expUnitHom x)⁻¹ * (expUnitHom y)⁻¹ :
      (Matrix (Fin 3) (Fin 3) A)ˣ) : Matrix (Fin 3) (Fin 3) A) =
      1 + (nilpotentMatrix x * nilpotentMatrix y -
        nilpotentMatrix y * nilpotentMatrix x) := by
  have h := congrArg (matrixUnitHom (A := A))
    (unitriangular_commutator (expCoordinates x) (expCoordinates y))
  simp only [map_mul, map_inv] at h
  have hm := congrArg Units.val h
  change ((expUnitHom x * expUnitHom y * (expUnitHom x)⁻¹ * (expUnitHom y)⁻¹ :
      (Matrix (Fin 3) (Fin 3) A)ˣ) : Matrix (Fin 3) (Fin 3) A) =
    toMatrix ⟨0, 0, x.a * y.b - y.a * x.b⟩ at hm
  rw [hm, nilpotentMatrix_commutator]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix, nilpotentMatrix]

end Half

end InfoGeometry.Algebra.UnitriangularBCH
