import Mathlib.Tactic

/-!
# InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.RingHomMatrix

Lean port of the AFP `Jordan_Normal_Form.Ring_Hom_Matrix` conversion layer.

The AFP development uses a `real_embedding` class to move matrices over
`ℤ`, `ℚ`, or `ℝ` into real matrices before applying analytic matrix estimates.
This file keeps the same interface in Lean:

* `RealEmbedding α` is a ring-preserving map `α → ℝ` with the ceiling
  comparison needed to pull real upper bounds back to `α`;
* `matReal` is the entrywise matrix conversion, matching AFP `mat⇩ℝ`;
* standard matrix operations commute with this conversion.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.RingHomMatrix

open scoped BigOperators

/-- Ordered ring embedding into the reals, matching AFP `real_embedding`. -/
class RealEmbedding (α : Type*) [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] where
  /-- The native multiplicative and additive embedding into the reals. -/
  toRingHom : α →+* ℝ
  /-- Real upper bounds pull back to integer-ceiling bounds in the source ring. -/
  le_ceil : ∀ {x : α} {z : ℝ}, toRingHom x ≤ z → x ≤ (Int.ceil z : α)

namespace RealEmbedding

variable {α : Type*} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] [RealEmbedding α]

/-! Compatibility readouts for the historical scalar-conversion interface. -/

def toReal (x : α) : ℝ :=
  RealEmbedding.toRingHom x

/-- The scalar real conversion attached to a `RealEmbedding`. -/
def realOf (x : α) : ℝ :=
  RealEmbedding.toReal x

@[simp]
theorem realOf_zero : realOf (0 : α) = 0 :=
  RealEmbedding.toRingHom.map_zero

@[simp]
theorem realOf_one : realOf (1 : α) = 1 :=
  RealEmbedding.toRingHom.map_one

@[simp]
theorem realOf_add (x y : α) : realOf (x + y) = realOf x + realOf y :=
  RealEmbedding.toRingHom.map_add x y

@[simp]
theorem realOf_mul (x y : α) : realOf (x * y) = realOf x * realOf y :=
  RealEmbedding.toRingHom.map_mul x y

@[simp]
theorem toRingHom_apply (x : α) : toRingHom x = realOf x :=
  rfl

@[simp]
theorem toRingHom_apply_toReal (x : α) : toRingHom x = RealEmbedding.toReal x :=
  rfl

theorem realOf_le_ceil {x : α} {z : ℝ} (h : realOf x ≤ z) :
    x ≤ (Int.ceil z : α) :=
  RealEmbedding.le_ceil h

end RealEmbedding

instance : RealEmbedding ℝ where
  toRingHom := RingHom.id ℝ
  le_ceil := by
    intro x z h
    exact le_trans h (Int.le_ceil z)

instance : RealEmbedding ℤ where
  toRingHom :=
    { toFun := fun x => x
      map_one' := by norm_num
      map_mul' := by intro x y; norm_num
      map_zero' := by norm_num
      map_add' := by intro x y; norm_num }
  le_ceil := by
    intro x z h
    change (x : ℝ) ≤ z at h
    exact_mod_cast (le_trans h (Int.le_ceil z))

instance : RealEmbedding ℚ where
  toRingHom :=
    { toFun := fun x => x
      map_one' := by norm_num
      map_mul' := by intro x y; norm_num
      map_zero' := by norm_num
      map_add' := by intro x y; norm_num }
  le_ceil := by
    intro x z h
    change (x : ℝ) ≤ z at h
    exact_mod_cast (le_trans h (Int.le_ceil z))

/-- AFP `mat_real`: entrywise conversion of a matrix into a real matrix. -/
def matReal {α m n : Type*}
    [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] [RealEmbedding α]
    (A : Matrix m n α) : Matrix m n ℝ :=
  A.map RealEmbedding.realOf

@[inherit_doc matReal]
scoped notation "matℝ" => matReal

@[simp]
theorem matReal_apply {α m n : Type*}
    [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] [RealEmbedding α]
    (A : Matrix m n α) (i : m) (j : n) :
    matReal A i j = RealEmbedding.realOf (A i j) :=
  rfl

theorem matReal_eq_mapMatrix {α n : Type*} [Fintype n] [DecidableEq n]
    [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] [RealEmbedding α]
    (A : Matrix n n α) :
    matReal A = RealEmbedding.toRingHom.mapMatrix A :=
  rfl

@[simp]
theorem matReal_zero {α m n : Type*}
    [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] [RealEmbedding α] :
    matReal (0 : Matrix m n α) = 0 := by
  ext i j
  simp [matReal]

@[simp]
theorem matReal_one {α n : Type*}
    [Fintype n] [DecidableEq n]
    [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] [RealEmbedding α] :
    matReal (1 : Matrix n n α) = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [matReal]
  · simp [matReal, h]

@[simp]
theorem matReal_add {α m n : Type*}
    [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] [RealEmbedding α]
    (A B : Matrix m n α) :
    matReal (A + B) = matReal A + matReal B := by
  ext i j
  simp [matReal]

@[simp]
theorem matReal_neg {α m n : Type*}
    [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] [RealEmbedding α]
    (A : Matrix m n α) :
    matReal (-A) = -matReal A := by
  ext i j
  simpa [matReal] using map_neg RealEmbedding.toRingHom (A i j)

@[simp]
theorem matReal_sub {α m n : Type*}
    [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] [RealEmbedding α]
    (A B : Matrix m n α) :
    matReal (A - B) = matReal A - matReal B := by
  ext i j
  simpa [matReal] using map_sub RealEmbedding.toRingHom (A i j) (B i j)

@[simp]
theorem matReal_mul {α m n p : Type*} [Fintype n]
    [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] [RealEmbedding α]
    (A : Matrix m n α) (B : Matrix n p α) :
    matReal (A * B) = matReal A * matReal B := by
  ext i j
  simp only [matReal, Matrix.mul_apply, Matrix.map_apply]
  change RealEmbedding.toRingHom (∑ x : n, A i x * B x j) =
    ∑ x : n, RealEmbedding.realOf (A i x) * RealEmbedding.realOf (B x j)
  rw [map_sum RealEmbedding.toRingHom]
  apply Finset.sum_congr rfl
  intro x _
  simp [RealEmbedding.realOf_mul]

@[simp]
theorem matReal_pow {α n : Type*}
    [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] [RealEmbedding α]
    [Fintype n] [DecidableEq n] (A : Matrix n n α) (k : ℕ) :
    matReal (A ^ k) = matReal A ^ k := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      simp [pow_succ, ih, matReal_mul]

theorem matReal_det {α n : Type*} [Fintype n] [DecidableEq n]
    [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] [RealEmbedding α]
    (A : Matrix n n α) :
    Matrix.det (matReal A) = RealEmbedding.realOf (Matrix.det A) := by
  rw [matReal_eq_mapMatrix]
  exact (RingHom.map_det RealEmbedding.toRingHom A).symm

theorem realOf_det {α n : Type*} [Fintype n] [DecidableEq n]
    [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] [RealEmbedding α]
    (A : Matrix n n α) :
    RealEmbedding.realOf (Matrix.det A) = Matrix.det (matReal A) :=
  (matReal_det A).symm

theorem matReal_entry_le_ceil {α m n : Type*}
    [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] [RealEmbedding α]
    {A : Matrix m n α} {i : m} {j : n} {z : ℝ}
    (h : matReal A i j ≤ z) :
    A i j ≤ (Int.ceil z : α) :=
  RealEmbedding.realOf_le_ceil h

end RingHomMatrix
