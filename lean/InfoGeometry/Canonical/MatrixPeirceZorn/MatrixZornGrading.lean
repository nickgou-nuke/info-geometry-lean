/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixPeirceZorn.MatrixZorn

/-!
# Matrix-valued Zorn grading defects and additive generation

The grading map has eigenvalues `0`, `1`, and `-1` on the four channels.
Its exact Leibniz defect is computed for the named nonassociative Zorn
product.  Explicit three-term decompositions prove additive generation of
each opposite channel, with arbitrary noncommutative matrix coefficients.
-/

namespace InfoGeometry.Canonical.MatrixPeirceZorn.Zorn.Grading

variable {n : Type*}

/-- The number grading, with signs on the two off-diagonal channels. -/
def number (X : Carrier n) : Carrier n := (0, X.2.1, -X.2.2.1, 0)

@[simp] theorem number_upper (u : Vec n) : number (upper u) = upper u := by
  simp [number, upper]

@[simp] theorem number_lower (u : Vec n) : number (lower u) = -lower u := by
  simp [number, lower]

@[simp] theorem number_corner (a b : Op n) : number (corner a b) = 0 := by
  simp [number, corner]

theorem number_add (X Y : Carrier n) : number (X + Y) = number X + number Y := by
  simp [number, add_comm]

variable [Fintype n] [DecidableEq n]

/-- The failure of the number grading to be a derivation of the Zorn product. -/
def leibnizDefect (X Y : Carrier n) : Carrier n :=
  number (mul X Y) - mul (number X) Y - mul X (number Y)

/-- The two same-channel cross products account for the whole Leibniz defect. -/
theorem leibnizDefect_eq_cross (X Y : Carrier n) :
    leibnizDefect X Y =
      -(3 • upper (cross X.2.2.1 Y.2.2.1)) -
        (3 • lower (cross X.2.1 Y.2.1)) := by
  apply Prod.ext
  · simp [leibnizDefect, number, mul, upper, lower, dot_eq]
    noncomm_ring
  · apply Prod.ext
    · funext i
      fin_cases i <;>
        simp [leibnizDefect, number, mul, upper, lower, cross,
          nsmul_eq_mul] <;>
        noncomm_ring
    · apply Prod.ext
      · funext i
        fin_cases i <;>
          simp [leibnizDefect, number, mul, upper, lower, left, right, cross,
            Matrix.vecHead, Matrix.vecTail,
            nsmul_eq_mul] <;>
          noncomm_ring
      · simp [leibnizDefect, number, mul, upper, lower, dot_eq]
        noncomm_ring

/-- Every matrix-valued triple is a sum of three cross products. -/
theorem three_cross_generation (v : Vec n) :
    cross ![0, 1, 0] ![0, 0, v 0] +
      cross ![0, 0, 1] ![v 1, 0, 0] +
      cross ![1, 0, 0] ![0, v 2, 0] = v := by
  funext i
  fin_cases i <;> simp [cross]

/-- Products of upper elements additively generate the full lower channel. -/
theorem lower_is_sum_of_three_upper_products (v : Vec n) :
    lower v =
      mul (upper ![0, 1, 0]) (upper ![0, 0, v 0]) +
        mul (upper ![0, 0, 1]) (upper ![v 1, 0, 0]) +
        mul (upper ![1, 0, 0]) (upper ![0, v 2, 0]) := by
  rw [upper_mul_upper, upper_mul_upper, upper_mul_upper,
    ← lower_add, ← lower_add, three_cross_generation]

/-- Products of lower elements additively generate the full upper channel. -/
theorem upper_is_sum_of_three_lower_products (v : Vec n) :
    upper v =
      mul (lower ![0, -1, 0]) (lower ![0, 0, v 0]) +
        mul (lower ![0, 0, -1]) (lower ![v 1, 0, 0]) +
        mul (lower ![-1, 0, 0]) (lower ![0, v 2, 0]) := by
  rw [lower_mul_lower, lower_mul_lower, lower_mul_lower, ← upper_add, ← upper_add]
  congr 1
  funext i
  fin_cases i <;> simp [cross]

omit [DecidableEq n] in
/-- The self-cross product is precisely the vector of coefficient commutators. -/
theorem cross_self_eq_commutators (u : Vec n) :
    cross u u = ![opBracket (u 1) (u 2), opBracket (u 2) (u 0),
      opBracket (u 0) (u 1)] := rfl

omit [DecidableEq n] in
/-- A self-cross product vanishes exactly when all three coefficient pairs commute. -/
theorem cross_self_eq_zero_iff (u : Vec n) :
    cross u u = 0 ↔
      Commute (u 1) (u 2) ∧ Commute (u 2) (u 0) ∧ Commute (u 0) (u 1) := by
  constructor
  · intro h
    have h0 : u 1 * u 2 = u 2 * u 1 := by simpa [cross, sub_eq_zero] using congrFun h 0
    have h1 : u 2 * u 0 = u 0 * u 2 := by simpa [cross, sub_eq_zero] using congrFun h 1
    have h2 : u 0 * u 1 = u 1 * u 0 := by simpa [cross, sub_eq_zero] using congrFun h 2
    exact ⟨h0, h1, h2⟩
  · rintro ⟨h0, h1, h2⟩
    funext i
    fin_cases i <;> simp [cross, h0.eq, h1.eq, h2.eq]

omit [DecidableEq n] in
/-- Nonzero self-cross is equivalent to a genuinely noncommuting coefficient pair. -/
theorem cross_self_ne_zero_iff (u : Vec n) :
    cross u u ≠ 0 ↔
      ¬Commute (u 1) (u 2) ∨ ¬Commute (u 2) (u 0) ∨ ¬Commute (u 0) (u 1) := by
  rw [ne_eq, cross_self_eq_zero_iff]
  tauto

end InfoGeometry.Canonical.MatrixPeirceZorn.Zorn.Grading
