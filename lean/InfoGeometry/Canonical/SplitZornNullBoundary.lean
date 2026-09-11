import InfoGeometry.Algebra.Zorn.ConcreteComposition
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Split Zorn null boundary spine

This file anchors the split-octonion/Zorn boundary story in theorem-safe finite
algebra.  It uses the existing concrete Zorn-cell owner
`InfoGeometry.Algebra.Zorn.ConcreteComposition` and proves only kernel-checked
facts about the split determinant/null cone.

Boundary: no global Cantor-fractal boundary theorem, no `G₂(2)` automorphism
theorem, no split exceptional-group closure, and no GNS quotient identification
is claimed here.  The closed content is the finite split-null spine that such
future constructions may map into.

#### BUCKET 1: CLOSED FINITE THEOREMS
The file proves a concrete nonzero Zorn null element over `ℝ`, its square-zero
law, determinant-zero after squaring, null absorption under Zorn multiplication,
norm-one determinant preservation, and self-polarization of the null generator.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The null-absorption and norm-one preservation theorems are conditional only on
the explicitly named determinant hypotheses `detZ X = 0` or `detZ U = 1`.

#### BUCKET 3: OPEN CLOSURE DEBT
No projective Cantor-colimit boundary theorem, no split exceptional-group
closure theorem, and no GNS quotient/null-ideal identification is claimed here.
-/

namespace InfoGeometry.Canonical.SplitZornNullBoundary

open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell

/-- Coordinatewise zero Zorn cell over `ℝ`, used only as a finite boundary witness. -/
def zornZero : ZornCell ℝ where
  r := 0
  s := 0
  x1 := 0
  x2 := 0
  x3 := 0
  y1 := 0
  y2 := 0
  y3 := 0

/-- A concrete top-right Zorn null generator over `ℝ`. -/
def zornTopRightNull : ZornCell ℝ where
  r := 0
  s := 0
  x1 := 1
  x2 := 0
  x3 := 0
  y1 := 0
  y2 := 0
  y3 := 0

@[simp] theorem zornTopRightNull_detZ :
    detZ zornTopRightNull = 0 := by
  norm_num [zornTopRightNull, detZ]

/-- The top-right Zorn null generator is nonzero, so the split null cone is nontrivial. -/
theorem zornTopRightNull_ne_zero :
    zornTopRightNull ≠ zornZero := by
  intro h
  have hx1 : zornTopRightNull.x1 = zornZero.x1 := by rw [h]
  norm_num [zornTopRightNull, zornZero] at hx1

/-- The split Zorn null cone over `ℝ` contains a nonzero point. -/
theorem exists_nonzero_zorn_null :
    ∃ X : ZornCell ℝ, X ≠ zornZero ∧ detZ X = 0 :=
  ⟨zornTopRightNull, zornTopRightNull_ne_zero, zornTopRightNull_detZ⟩

/-- The top-right Zorn null generator is square-zero for the concrete Zorn product. -/
theorem zornTopRightNull_sq_zero :
    zornTopRightNull * zornTopRightNull = zornZero := by
  change mulZ zornTopRightNull zornTopRightNull = zornZero
  unfold mulZ zornTopRightNull zornZero
  rw [ZornCell.mk.injEq]
  repeat constructor <;> norm_num

/-- A square-zero Zorn null boundary mode has zero determinant after squaring. -/
theorem zornTopRightNull_sq_detZ_zero :
    detZ (zornTopRightNull * zornTopRightNull) = 0 := by
  rw [zornTopRightNull_sq_zero]
  norm_num [detZ, zornZero]

/-- Left multiplication by a Zorn-null element lands in the Zorn null cone. -/
theorem left_null_absorbs_to_null
    (X Y : ZornCell ℝ) (hX : detZ X = 0) :
    detZ (X * Y) = 0 :=
  detZ_mul_eq_zero_of_left_null X Y hX

/-- Right multiplication by a Zorn-null element lands in the Zorn null cone. -/
theorem right_null_absorbs_to_null
    (X Y : ZornCell ℝ) (hY : detZ Y = 0) :
    detZ (X * Y) = 0 :=
  detZ_mul_eq_zero_of_right_null X Y hY

/-- Multiplication by a determinant-one Zorn cell preserves the split determinant on the left. -/
theorem normOne_left_preserves_detZ
    (U X : ZornCell ℝ) (hU : detZ U = 1) :
    detZ (U * X) = detZ X :=
  detZ_left_mul_normOne U X hU

/-- Multiplication by a determinant-one Zorn cell preserves the split determinant on the right. -/
theorem normOne_right_preserves_detZ
    (X U : ZornCell ℝ) (hU : detZ U = 1) :
    detZ (X * U) = detZ X :=
  detZ_right_mul_normOne X U hU

/-- Determinant-one Zorn cells preserve nullness on the left. -/
theorem normOne_left_preserves_null
    (U X : ZornCell ℝ) (hU : detZ U = 1) (hX : detZ X = 0) :
    detZ (U * X) = 0 := by
  rw [normOne_left_preserves_detZ U X hU, hX]

/-- Determinant-one Zorn cells preserve nullness on the right. -/
theorem normOne_right_preserves_null
    (X U : ZornCell ℝ) (hU : detZ U = 1) (hX : detZ X = 0) :
    detZ (X * U) = 0 := by
  rw [normOne_right_preserves_detZ X U hU, hX]

/-- Polar self-orthogonality of the concrete top-right null generator. -/
theorem zornTopRightNull_polar_self_zero :
    polarZ zornTopRightNull zornTopRightNull = 0 :=
  polarZ_self_of_detZ_zero zornTopRightNull zornTopRightNull_detZ

/-- Finite split-null boundary packet: a nonzero null, square-zero Zorn mode. -/
theorem split_zorn_null_boundary_packet :
    zornTopRightNull ≠ zornZero ∧
      detZ zornTopRightNull = 0 ∧
      zornTopRightNull * zornTopRightNull = zornZero ∧
      polarZ zornTopRightNull zornTopRightNull = 0 :=
  ⟨zornTopRightNull_ne_zero,
    zornTopRightNull_detZ,
    zornTopRightNull_sq_zero,
    zornTopRightNull_polar_self_zero⟩

end InfoGeometry.Canonical.SplitZornNullBoundary
