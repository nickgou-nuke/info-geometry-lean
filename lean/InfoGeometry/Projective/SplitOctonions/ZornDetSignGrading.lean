import InfoGeometry.Projective.SplitOctonions
import Mathlib.Tactic

/-!
# Zorn determinant sign grading

This file formalizes the determinant-sign split of the concrete Zorn
split-octonion cell.

On the non-null locus `detZ3 X ≠ 0`, the sign of the Zorn determinant gives
a multiplicative `Z₂` sector:

* `detZ3 X > 0` is the even/positive bulk sector;
* `detZ3 X < 0` is the odd/negative bulk sector;
* `detZ3 X = 0` is the boundary/null shell.

The sign operator

  Γ f X = sign(detZ3 X) * f X

is an involution only on the non-null locus.  On the boundary, the sign
collapses to zero.

This file does not claim a Lie superalgebra structure on raw Zorn cells.
The Zorn product is nonassociative; the superbracket below is only the
binary graded commutator expression on homogeneous bulk sectors.
-/

namespace InfoGeometry.Projective.SplitOctonions

namespace ZornCell

noncomputable section
open Classical

/-! ## Bulk sectors and boundary -/

/-- Concrete Zorn bulk: determinant is nonzero. -/
def IsBulk (X : ZornCell ℝ (ℝ × ℝ × ℝ)) : Prop :=
  detZ3 X ≠ 0

/-- Positive/even determinant sector. -/
def IsPositiveSector (X : ZornCell ℝ (ℝ × ℝ × ℝ)) : Prop :=
  0 < detZ3 X

/-- Negative/odd determinant sector. -/
def IsNegativeSector (X : ZornCell ℝ (ℝ × ℝ × ℝ)) : Prop :=
  detZ3 X < 0

/-- Boundary/null sector. This is the projective isotropic shell. -/
def IsBoundarySector (X : ZornCell ℝ (ℝ × ℝ × ℝ)) : Prop :=
  detZ3 X = 0

/--
Majorana boundary support.

This is deliberately just the determinant-null boundary predicate.
No current algebra or Clifford-mode theorem is claimed here.
-/
def IsMajoranaBoundary (X : ZornCell ℝ (ℝ × ℝ × ℝ)) : Prop :=
  IsBoundarySector X

/--
A bulk point is exactly either positive or negative determinant.
-/
theorem isBulk_iff_positive_or_negative
    (X : ZornCell ℝ (ℝ × ℝ × ℝ)) :
    IsBulk X ↔ IsPositiveSector X ∨ IsNegativeSector X := by
  unfold IsBulk IsPositiveSector IsNegativeSector
  constructor
  · intro h
    have h0 : (0 : ℝ) ≠ detZ3 X := by
      exact Ne.symm h
    exact lt_or_gt_of_ne h0
  · intro h
    rcases h with hpos | hneg
    · exact ne_of_gt hpos
    · exact ne_of_lt hneg

/-! ## Determinant sign -/

/--
The determinant sign.

It is `1` on the positive sector, `-1` on the negative sector,
and `0` on the boundary.
-/
def zornDetSign (X : ZornCell ℝ (ℝ × ℝ × ℝ)) : ℝ :=
  if 0 < detZ3 X then 1
  else if detZ3 X < 0 then -1
  else 0

@[simp]
theorem zornDetSign_eq_one_of_positive
    (X : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : IsPositiveSector X) :
    zornDetSign X = 1 := by
  unfold IsPositiveSector at hX
  unfold zornDetSign
  simp [hX]

@[simp]
theorem zornDetSign_eq_neg_one_of_negative
    (X : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : IsNegativeSector X) :
    zornDetSign X = -1 := by
  unfold IsNegativeSector at hX
  have hnot : ¬ 0 < detZ3 X := not_lt.mpr (le_of_lt hX)
  simp [zornDetSign, hnot, hX]

/--
The determinant sign vanishes exactly on the boundary.
-/
theorem zornDetSign_eq_zero_iff_boundary
    (X : ZornCell ℝ (ℝ × ℝ × ℝ)) :
    zornDetSign X = 0 ↔ IsBoundarySector X := by
  constructor
  · intro hs
    unfold IsBoundarySector
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hsign := zornDetSign_eq_neg_one_of_negative X hneg
      rw [hsign] at hs
      norm_num at hs
    · have hsign := zornDetSign_eq_one_of_positive X hpos
      rw [hsign] at hs
      norm_num at hs
  · intro hb
    unfold IsBoundarySector at hb
    unfold zornDetSign
    simp [hb]

/--
On the bulk, the determinant sign squares to `1`.
-/
theorem zornDetSign_sq_of_bulk
    (X : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : IsBulk X) :
    zornDetSign X * zornDetSign X = 1 := by
  unfold IsBulk at hX
  rcases lt_or_gt_of_ne hX.symm with hpos | hneg
  · rw [zornDetSign_eq_one_of_positive X hpos]
    ring
  · rw [zornDetSign_eq_neg_one_of_negative X hneg]
    ring

/-! ## Product sector laws -/

/-- Positive times positive is positive. -/
theorem positiveSector_mul3_positive
    (X Y : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : IsPositiveSector X) (hY : IsPositiveSector Y) :
    IsPositiveSector (mul3 X Y) := by
  unfold IsPositiveSector at *
  rw [detZ3_mul3]
  exact mul_pos hX hY

/-- Positive times negative is negative. -/
theorem positiveSector_mul3_negative
    (X Y : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : IsPositiveSector X) (hY : IsNegativeSector Y) :
    IsNegativeSector (mul3 X Y) := by
  unfold IsPositiveSector IsNegativeSector at *
  rw [detZ3_mul3]
  exact mul_neg_of_pos_of_neg hX hY

/-- Negative times positive is negative. -/
theorem negativeSector_mul3_positive
    (X Y : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : IsNegativeSector X) (hY : IsPositiveSector Y) :
    IsNegativeSector (mul3 X Y) := by
  unfold IsPositiveSector IsNegativeSector at *
  rw [detZ3_mul3]
  exact mul_neg_of_neg_of_pos hX hY

/-- Negative times negative is positive. -/
theorem negativeSector_mul3_negative
    (X Y : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : IsNegativeSector X) (hY : IsNegativeSector Y) :
    IsPositiveSector (mul3 X Y) := by
  unfold IsPositiveSector IsNegativeSector at *
  rw [detZ3_mul3]
  exact mul_pos_of_neg_of_neg hX hY

/--
The bulk is closed under Zorn multiplication.
-/
theorem bulk_mul3_of_bulk
    (X Y : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : IsBulk X) (hY : IsBulk Y) :
    IsBulk (mul3 X Y) := by
  unfold IsBulk at *
  rw [detZ3_mul3]
  exact mul_ne_zero hX hY

/--
The determinant sign is multiplicative on the non-null/bulk locus.

This is the exact `Z₂` grading law induced by the Zorn determinant.
-/
theorem zornDetSign_mul3_of_bulk
    (X Y : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : IsBulk X) (hY : IsBulk Y) :
    zornDetSign (mul3 X Y) = zornDetSign X * zornDetSign Y := by
  unfold IsBulk at hX hY
  rcases lt_or_gt_of_ne hX.symm with hXp | hXn
  · rcases lt_or_gt_of_ne hY.symm with hYp | hYn
    · have hXY : IsPositiveSector (mul3 X Y) :=
        positiveSector_mul3_positive X Y hXp hYp
      rw [zornDetSign_eq_one_of_positive (mul3 X Y) hXY]
      rw [zornDetSign_eq_one_of_positive X hXp]
      rw [zornDetSign_eq_one_of_positive Y hYp]
      ring
    · have hXY : IsNegativeSector (mul3 X Y) :=
        positiveSector_mul3_negative X Y hXp hYn
      rw [zornDetSign_eq_neg_one_of_negative (mul3 X Y) hXY]
      rw [zornDetSign_eq_one_of_positive X hXp]
      rw [zornDetSign_eq_neg_one_of_negative Y hYn]
      ring
  · rcases lt_or_gt_of_ne hY.symm with hYp | hYn
    · have hXY : IsNegativeSector (mul3 X Y) :=
        negativeSector_mul3_positive X Y hXn hYp
      rw [zornDetSign_eq_neg_one_of_negative (mul3 X Y) hXY]
      rw [zornDetSign_eq_neg_one_of_negative X hXn]
      rw [zornDetSign_eq_one_of_positive Y hYp]
      ring
    · have hXY : IsPositiveSector (mul3 X Y) :=
        negativeSector_mul3_negative X Y hXn hYn
      rw [zornDetSign_eq_one_of_positive (mul3 X Y) hXY]
      rw [zornDetSign_eq_neg_one_of_negative X hXn]
      rw [zornDetSign_eq_neg_one_of_negative Y hYn]
      ring

/-! ## Sign operator Γ -/

/--
The determinant-sign operator on scalar functions on Zorn cells.

  Γ f X = sign(detZ3 X) * f X.
-/
noncomputable def zornGamma
    (f : ZornCell ℝ (ℝ × ℝ × ℝ) → ℝ) :
    ZornCell ℝ (ℝ × ℝ × ℝ) → ℝ :=
  fun X => zornDetSign X * f X

/--
`Γ² = 1` pointwise on the bulk.
-/
theorem zornGamma_sq_apply_of_bulk
    (f : ZornCell ℝ (ℝ × ℝ × ℝ) → ℝ)
    (X : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : IsBulk X) :
    zornGamma (zornGamma f) X = f X := by
  unfold zornGamma
  calc
    zornDetSign X * (zornDetSign X * f X)
        = (zornDetSign X * zornDetSign X) * f X := by ring
    _ = 1 * f X := by rw [zornDetSign_sq_of_bulk X hX]
    _ = f X := by ring

/--
On the boundary, Γ annihilates scalar functions.
-/
theorem zornGamma_apply_boundary
    (f : ZornCell ℝ (ℝ × ℝ × ℝ) → ℝ)
    (X : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : IsBoundarySector X) :
    zornGamma f X = 0 := by
  unfold zornGamma
  rw [(zornDetSign_eq_zero_iff_boundary X).2 hX]
  simp

/--
Majorana boundary equivalence: the determinant sign collapses exactly on the
Majorana/null boundary.
-/
theorem isMajoranaBoundary_iff_detSign_zero
    (X : ZornCell ℝ (ℝ × ℝ × ℝ)) :
    IsMajoranaBoundary X ↔ zornDetSign X = 0 := by
  unfold IsMajoranaBoundary IsBoundarySector
  exact (zornDetSign_eq_zero_iff_boundary X).symm

/-! ## Formal graded commutator expression -/

/-- Componentwise addition of concrete Zorn cells. -/
def cellAdd
    (X Y : ZornCell ℝ (ℝ × ℝ × ℝ)) :
    ZornCell ℝ (ℝ × ℝ × ℝ) where
  a := X.a + Y.a
  b := X.b + Y.b
  v := X.v + Y.v
  w := X.w + Y.w

/-- Componentwise negation of concrete Zorn cells. -/
def cellNeg
    (X : ZornCell ℝ (ℝ × ℝ × ℝ)) :
    ZornCell ℝ (ℝ × ℝ × ℝ) where
  a := -X.a
  b := -X.b
  v := -X.v
  w := -X.w

/-- Componentwise subtraction of concrete Zorn cells. -/
def cellSub
    (X Y : ZornCell ℝ (ℝ × ℝ × ℝ)) :
    ZornCell ℝ (ℝ × ℝ × ℝ) :=
  cellAdd X (cellNeg Y)

/--
Formal determinant-graded Zorn superbracket.

If both entries are in the negative/odd bulk sector, this is the
anticommutator-like expression

  X⋆Y + Y⋆X.

Otherwise it is the commutator-like expression

  X⋆Y - Y⋆X.

Because Zorn multiplication is nonassociative, this is not asserted to satisfy
a Lie-superalgebra Jacobi identity.
-/
noncomputable def zornSuperBracket
    (X Y : ZornCell ℝ (ℝ × ℝ × ℝ)) :
    ZornCell ℝ (ℝ × ℝ × ℝ) := by
  classical
  exact
    if IsNegativeSector X ∧ IsNegativeSector Y then
      cellAdd (mul3 X Y) (mul3 Y X)
    else
      cellSub (mul3 X Y) (mul3 Y X)

/-- Odd-odd sector gives the anticommutator expression. -/
theorem zornSuperBracket_odd_odd
    (X Y : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : IsNegativeSector X) (hY : IsNegativeSector Y) :
    zornSuperBracket X Y = cellAdd (mul3 X Y) (mul3 Y X) := by
  classical
  unfold zornSuperBracket
  simp [hX, hY]

/-- Outside odd-odd, the bracket is the commutator expression. -/
theorem zornSuperBracket_not_odd_odd
    (X Y : ZornCell ℝ (ℝ × ℝ × ℝ))
    (h : ¬ (IsNegativeSector X ∧ IsNegativeSector Y)) :
    zornSuperBracket X Y = cellSub (mul3 X Y) (mul3 Y X) := by
  classical
  unfold zornSuperBracket
  simp [h]

end

end ZornCell

end InfoGeometry.Projective.SplitOctonions
