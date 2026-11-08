/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Abel

/-!
# Matrix-valued triples and the explicit Zorn product

All coefficients are arbitrary complex square matrices. Their multiplication is
mathlib's native associative matrix multiplication. The named `mul` on the
native product carrier is a different, generally nonassociative operation.
No multiplication or ring instance for that operation is declared.
-/

namespace InfoGeometry.Canonical.MatrixPeirceZorn.Zorn

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev Op (n : Type*) := Matrix n n ℂ
abbrev Vec (n : Type*) := Fin 3 → Op n
abbrev Carrier (n : Type*) := Op n × Vec n × Vec n × Op n

abbrev matrixCoefficient (n : Type*) := Matrix n n ℂ

def dot (u v : Vec n) : Op n := dotProduct u v

def cross (u v : Vec n) : Vec n :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

def left (a : Op n) (v : Vec n) : Vec n := fun i => a * v i

def right (v : Vec n) (b : Op n) : Vec n := fun i => v i * b

def opBracket (a b : Op n) : Op n := a * b - b * a

def crossDefect (u v : Vec n) : Vec n := cross u v + cross v u

def mul (X Y : Carrier n) : Carrier n :=
  (X.1 * Y.1 + dot X.2.1 Y.2.2.1,
   left X.1 Y.2.1 + right X.2.1 Y.2.2.2 - cross X.2.2.1 Y.2.2.1,
   right X.2.2.1 Y.1 + left X.2.2.2 Y.2.2.1 + cross X.2.1 Y.2.1,
   dot X.2.2.1 Y.2.1 + X.2.2.2 * Y.2.2.2)

def bracket (X Y : Carrier n) : Carrier n := mul X Y - mul Y X

def associator (X Y Z : Carrier n) : Carrier n :=
  mul (mul X Y) Z - mul X (mul Y Z)

def jacobiator (X Y Z : Carrier n) : Carrier n :=
  bracket (bracket X Y) Z + bracket (bracket Y Z) X + bracket (bracket Z X) Y

def upper (u : Vec n) : Carrier n := (0, u, 0, 0)

def lower (w : Vec n) : Carrier n := (0, 0, w, 0)

def corner (a b : Op n) : Carrier n := (a, 0, 0, b)

def ePlus : Carrier n := corner 1 0

def eMinus : Carrier n := corner 0 1

omit [DecidableEq n] in
lemma dot_eq (u v : Vec n) :
    dot u v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [dot, dotProduct, Fin.sum_univ_succ, add_assoc]

@[simp] lemma cross_zero (u : Vec n) : cross u 0 = 0 := by
  funext i
  fin_cases i <;> simp [cross]

@[simp] lemma zero_cross (u : Vec n) : cross 0 u = 0 := by
  funext i
  fin_cases i <;> simp [cross]

@[simp] lemma left_zero (a : Op n) : left a 0 = 0 := by
  funext i
  simp [left]

@[simp] lemma zero_left (u : Vec n) : left 0 u = 0 := by
  funext i
  simp [left]

@[simp] lemma right_zero (u : Vec n) : right u 0 = 0 := by
  funext i
  simp [right]

@[simp] lemma zero_right (a : Op n) : right 0 a = 0 := by
  funext i
  simp [right]

omit [DecidableEq n] in
@[simp] lemma dot_zero (u : Vec n) : dot u 0 = 0 := by simp [dot]
omit [DecidableEq n] in
@[simp] lemma zero_dot (u : Vec n) : dot 0 u = 0 := by simp [dot]

lemma bac_cab (u w v : Vec n) :
    left (dot u w) v - right u (dot w v) =
      cross (cross u w) v - cross u (cross w v) := by
  funext i
  fin_cases i <;> simp [left, right, dot_eq, cross] <;> noncomm_ring

omit [DecidableEq n] in
lemma cross_symmetry_defect (u v : Vec n) :
    crossDefect u v =
      ![opBracket (u 1) (v 2) - opBracket (u 2) (v 1),
        opBracket (u 2) (v 0) - opBracket (u 0) (v 2),
        opBracket (u 0) (v 1) - opBracket (u 1) (v 0)] := by
  funext i
  fin_cases i <;> simp [crossDefect, cross, opBracket] <;> noncomm_ring

lemma cross_add (u v w : Vec n) : cross u (v + w) = cross u v + cross u w := by
  funext i
  fin_cases i <;> simp [cross] <;> noncomm_ring

lemma add_cross (u v w : Vec n) : cross (u + v) w = cross u w + cross v w := by
  funext i
  fin_cases i <;> simp [cross] <;> noncomm_ring

lemma left_add (a : Op n) (u v : Vec n) : left a (u + v) = left a u + left a v := by
  funext i
  simp [left, _root_.mul_add]

lemma add_left (a b : Op n) (u : Vec n) : left (a + b) u = left a u + left b u := by
  funext i
  simp [left, _root_.add_mul]

lemma right_add (u : Vec n) (a b : Op n) : right u (a + b) = right u a + right u b := by
  funext i
  simp [right, _root_.mul_add]

lemma add_right (u v : Vec n) (a : Op n) : right (u + v) a = right u a + right v a := by
  funext i
  simp [right, _root_.add_mul]

omit [DecidableEq n] in
@[simp] lemma cross_neg (u v : Vec n) : cross u (-v) = -cross u v := by
  funext i
  fin_cases i <;> simp [cross] <;> noncomm_ring

omit [DecidableEq n] in
@[simp] lemma neg_cross (u v : Vec n) : cross (-u) v = -cross u v := by
  funext i
  fin_cases i <;> simp [cross] <;> noncomm_ring

lemma mul_add (X Y Z : Carrier n) : mul X (Y + Z) = mul X Y + mul X Z := by
  apply Prod.ext
  · simp [mul, dot, dotProduct_add, _root_.mul_add]
    abel
  · apply Prod.ext
    · simp only [mul, Prod.fst_add, Prod.snd_add, left_add, right_add, cross_add]
      abel
    · apply Prod.ext
      · simp only [mul, Prod.fst_add, Prod.snd_add, left_add, right_add, cross_add]
        abel
      · simp [mul, dot, dotProduct_add, _root_.mul_add]
        abel

lemma add_mul (X Y Z : Carrier n) : mul (X + Y) Z = mul X Z + mul Y Z := by
  apply Prod.ext
  · simp [mul, dot, add_dotProduct, _root_.add_mul]
    abel
  · apply Prod.ext
    · simp only [mul, Prod.fst_add, Prod.snd_add, add_left, add_right, add_cross]
      abel
    · apply Prod.ext
      · simp only [mul, Prod.fst_add, Prod.snd_add, add_left, add_right, add_cross]
        abel
      · simp [mul, dot, add_dotProduct, _root_.add_mul]
        abel

@[simp] lemma mul_zero (X : Carrier n) : mul X 0 = 0 := by
  simp [mul]

@[simp] lemma zero_mul (X : Carrier n) : mul 0 X = 0 := by
  simp [mul]

lemma mul_sub (X Y Z : Carrier n) : mul X (Y - Z) = mul X Y - mul X Z := by
  have h := mul_add X (Y - Z) Z
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

lemma sub_mul (X Y Z : Carrier n) : mul (X - Y) Z = mul X Z - mul Y Z := by
  have h := add_mul (X - Y) Y Z
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

@[simp] lemma mul_neg (X Y : Carrier n) : mul X (-Y) = -mul X Y := by
  simpa using mul_sub X 0 Y

@[simp] lemma neg_mul (X Y : Carrier n) : mul (-X) Y = -mul X Y := by
  simpa using sub_mul 0 X Y

omit [Fintype n] [DecidableEq n] in
lemma four_block_decomposition (X : Carrier n) :
    X = corner X.1 0 + upper X.2.1 + lower X.2.2.1 + corner 0 X.2.2.2 := by
  simp [corner, upper, lower]

omit [Fintype n] [DecidableEq n] in
@[simp] lemma upper_add (u v : Vec n) : upper (u + v) = upper u + upper v := by
  simp [upper]

omit [Fintype n] [DecidableEq n] in
@[simp] lemma lower_add (u v : Vec n) : lower (u + v) = lower u + lower v := by
  simp [lower]

omit [Fintype n] [DecidableEq n] in
@[simp] lemma upper_sub (u v : Vec n) : upper (u - v) = upper u - upper v := by
  simp [upper]

omit [Fintype n] [DecidableEq n] in
@[simp] lemma lower_sub (u v : Vec n) : lower (u - v) = lower u - lower v := by
  simp [lower]

omit [Fintype n] [DecidableEq n] in
@[simp] lemma upper_neg (u : Vec n) : upper (-u) = -upper u := by simp [upper]
omit [Fintype n] [DecidableEq n] in
@[simp] lemma lower_neg (u : Vec n) : lower (-u) = -lower u := by simp [lower]
omit [Fintype n] [DecidableEq n] in
@[simp] lemma upper_zero : upper (0 : Vec n) = 0 := rfl
omit [Fintype n] [DecidableEq n] in
@[simp] lemma lower_zero : lower (0 : Vec n) = 0 := rfl

lemma upper_mul_upper (u v : Vec n) : mul (upper u) (upper v) = lower (cross u v) := by
  simp [mul, upper, lower]

lemma lower_mul_lower (u v : Vec n) : mul (lower u) (lower v) = upper (-cross u v) := by
  simp [mul, upper, lower]

lemma upper_mul_lower (u v : Vec n) : mul (upper u) (lower v) = corner (dot u v) 0 := by
  simp [mul, upper, lower, corner]

lemma lower_mul_upper (u v : Vec n) : mul (lower u) (upper v) = corner 0 (dot u v) := by
  simp [mul, upper, lower, corner]

lemma corner_mul_corner (a b c d : Op n) :
    mul (corner a b) (corner c d) = corner (a * c) (b * d) := by
  simp [mul, corner]

lemma corner_mul_upper (a b : Op n) (u : Vec n) :
    mul (corner a b) (upper u) = upper (left a u) := by
  simp [mul, corner, upper]

lemma upper_mul_corner (u : Vec n) (a b : Op n) :
    mul (upper u) (corner a b) = upper (right u b) := by
  simp [mul, corner, upper]

lemma corner_mul_lower (a b : Op n) (u : Vec n) :
    mul (corner a b) (lower u) = lower (left b u) := by
  simp [mul, corner, lower]

lemma lower_mul_corner (u : Vec n) (a b : Op n) :
    mul (lower u) (corner a b) = lower (right u a) := by
  simp [mul, corner, lower]

lemma ePlus_idempotent : mul (ePlus : Carrier n) ePlus = ePlus := by
  simp [ePlus, corner_mul_corner]

lemma eMinus_idempotent : mul (eMinus : Carrier n) eMinus = eMinus := by
  simp [eMinus, corner_mul_corner]

lemma ePlus_mul_eMinus : mul (ePlus : Carrier n) eMinus = 0 := by
  simp only [ePlus, eMinus, corner_mul_corner]
  simp [corner]

lemma eMinus_mul_ePlus : mul (eMinus : Carrier n) ePlus = 0 := by
  simp only [ePlus, eMinus, corner_mul_corner]
  simp [corner]

@[simp] lemma left_one (u : Vec n) : left 1 u = u := by
  funext i
  simp [left]

@[simp] lemma right_one (u : Vec n) : right u 1 = u := by
  funext i
  simp [right]

lemma unit_mul (X : Carrier n) : mul (corner 1 1) X = X := by
  rcases X with ⟨a, v, w, b⟩
  simp [mul, corner]

lemma mul_unit (X : Carrier n) : mul X (corner 1 1) = X := by
  rcases X with ⟨a, v, w, b⟩
  simp [mul, corner]

omit [Fintype n] in
lemma unit_eq_ePlus_add_eMinus : (corner 1 1 : Carrier n) = ePlus + eMinus := by
  simp [corner, ePlus, eMinus]

lemma peirce_pp (X : Carrier n) :
    mul (mul ePlus X) ePlus = corner X.1 0 := by
  simp [mul, ePlus, corner]

lemma peirce_pm (X : Carrier n) :
    mul (mul ePlus X) eMinus = upper X.2.1 := by
  simp [mul, ePlus, eMinus, corner, upper]

lemma peirce_mp (X : Carrier n) :
    mul (mul eMinus X) ePlus = lower X.2.2.1 := by
  simp [mul, ePlus, eMinus, corner, lower]

lemma peirce_mm (X : Carrier n) :
    mul (mul eMinus X) eMinus = corner 0 X.2.2.2 := by
  simp [mul, eMinus, corner]

lemma peirce_expansion (X : Carrier n) :
    X = mul (mul ePlus X) ePlus + mul (mul ePlus X) eMinus +
      mul (mul eMinus X) ePlus + mul (mul eMinus X) eMinus := by
  rw [peirce_pp, peirce_pm, peirce_mp, peirce_mm]
  exact four_block_decomposition X

omit [Fintype n] [DecidableEq n] in
lemma four_block_unique (a b : Op n) (u w : Vec n) (X : Carrier n) :
    corner a 0 + upper u + lower w + corner 0 b = X ↔
      a = X.1 ∧ u = X.2.1 ∧ w = X.2.2.1 ∧ b = X.2.2.2 := by
  simp [corner, upper, lower, Prod.ext_iff]

lemma associator_upper_lower_upper (u w v : Vec n) :
    associator (upper u) (lower w) (upper v) =
      upper (left (dot u w) v - right u (dot w v)) := by
  simp [associator, upper_mul_lower, lower_mul_upper,
    corner_mul_upper, upper_mul_corner]

lemma associator_upper_upper_lower (u w v : Vec n) :
    associator (upper u) (upper w) (lower v) =
      -upper (cross (cross u w) v) := by
  simp [associator, upper_mul_upper, upper_mul_lower,
    lower_mul_lower, upper_mul_corner]

lemma associator_lower_upper_upper (u w v : Vec n) :
    associator (lower u) (upper w) (upper v) =
      upper (cross u (cross w v)) := by
  simp [associator, lower_mul_upper, upper_mul_upper,
    corner_mul_upper, lower_mul_lower]

lemma associator_lower_upper_lower (u w v : Vec n) :
    associator (lower u) (upper w) (lower v) =
      lower (left (dot u w) v - right u (dot w v)) := by
  simp [associator, lower_mul_upper, upper_mul_lower,
    corner_mul_lower, lower_mul_corner]

lemma associator_lower_lower_upper (u w v : Vec n) :
    associator (lower u) (lower w) (upper v) =
      -lower (cross (cross u w) v) := by
  simp [associator, lower_mul_lower, lower_mul_upper,
    upper_mul_upper, lower_mul_corner]

lemma associator_upper_lower_lower (u w v : Vec n) :
    associator (upper u) (lower w) (lower v) =
      lower (cross u (cross w v)) := by
  simp [associator, upper_mul_lower, lower_mul_lower,
    corner_mul_lower, upper_mul_upper]

lemma mixed_associator_sum (w u v : Vec n) :
    associator (lower w) (upper u) (upper v) +
      associator (upper u) (upper v) (lower w) =
        upper (cross w (cross u v) - cross (cross u v) w) := by
  simp [associator_lower_upper_upper, associator_upper_upper_lower, sub_eq_add_neg]

lemma mixed_associator_difference (w u v : Vec n) :
    associator (lower w) (upper u) (upper v) -
      associator (upper u) (upper v) (lower w) =
        upper (crossDefect w (cross u v)) := by
  simp [associator_lower_upper_upper, associator_upper_upper_lower, crossDefect]

lemma associator_upper_upper_upper (u v w : Vec n) :
    associator (upper u) (upper v) (upper w) =
      corner (-(dot u (cross v w))) (dot (cross u v) w) := by
  simp [associator, upper_mul_upper, lower_mul_upper, upper_mul_lower, corner]

lemma associator_lower_lower_lower (u v w : Vec n) :
    associator (lower u) (lower v) (lower w) =
      corner (-(dot (cross u v) w)) (dot u (cross v w)) := by
  simp [associator, lower_mul_lower, upper_mul_lower, lower_mul_upper, corner]

lemma associator_upper_upper_corner (u v : Vec n) (a : Op n) :
    associator (upper u) (upper v) (corner a 0) =
      lower (right (cross u v) a) := by
  simp [associator, upper_mul_upper, lower_mul_corner, upper_mul_corner]

lemma bracket_upper_upper (u v : Vec n) :
    bracket (upper u) (upper v) = lower (cross u v - cross v u) := by
  simp [bracket, upper_mul_upper]

lemma bracket_lower_upper (u v : Vec n) :
    bracket (lower u) (upper v) = corner (-(dot v u)) (dot u v) := by
  simp [bracket, lower_mul_upper, upper_mul_lower, corner]

lemma jacobiator_upper_upper_upper (u v w : Vec n) :
    jacobiator (upper u) (upper v) (upper w) =
      corner
        (-(dot w (cross u v - cross v u)) - dot u (cross v w - cross w v) -
          dot v (cross w u - cross u w))
        (dot (cross u v - cross v u) w + dot (cross v w - cross w v) u +
          dot (cross w u - cross u w) v) := by
  unfold jacobiator
  rw [bracket_upper_upper, bracket_upper_upper, bracket_upper_upper]
  rw [bracket_lower_upper, bracket_lower_upper, bracket_lower_upper]
  simp [corner, sub_eq_add_neg]

end InfoGeometry.Canonical.MatrixPeirceZorn.Zorn
