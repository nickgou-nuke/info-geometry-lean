import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Projective.KleinCrossRatioInvariant

Concrete Klein/Erlangen projective-line invariant.

This file proves, over a commutative ring, the polynomial identities behind
the projective invariance of the cross-ratio:

* scaling homogeneous representatives scales numerator and denominator by the
  same factor;
* a `2 × 2` linear transformation scales every bracket by its determinant;
* therefore the cross-ratio is invariant in cross-multiplied form.

No wrappers. No `sorry`.
-/

namespace InfoGeometry.Projective.KleinCrossRatioInvariant

/-- Homogeneous coordinates `[x : y]` on a projective line. -/
structure HomPoint2 (R : Type*) where
  x : R
  y : R

namespace HomPoint2

variable {R : Type*} [CommRing R]

/-- The alternating bracket `x₁ y₂ - x₂ y₁`. -/
def bracket (P Q : HomPoint2 R) : R :=
  P.x * Q.y - Q.x * P.y

/-- Scalar rescaling of homogeneous coordinates. -/
def scale (l : R) (P : HomPoint2 R) : HomPoint2 R where
  x := l * P.x
  y := l * P.y

/-- Linear transformation represented by the matrix `[[a,b],[c,d]]`. -/
def lin (a b c d : R) (P : HomPoint2 R) : HomPoint2 R where
  x := a * P.x + b * P.y
  y := c * P.x + d * P.y

/-- Determinant of the matrix `[[a,b],[c,d]]`. -/
def det2 (a b c d : R) : R :=
  a * d - b * c

@[simp] theorem det2_identity :
    det2 (1 : R) 0 0 1 = 1 := by
  unfold det2
  ring

@[simp] theorem det2_duplicate_rows_zero (a b : R) :
    det2 a b a b = 0 := by
  unfold det2
  ring

@[simp] theorem det2_duplicate_cols_zero (a b : R) :
    det2 a a b b = 0 := by
  unfold det2
  ring

@[simp] theorem det2_swap_rows (a b c d : R) :
    det2 c d a b = -det2 a b c d := by
  unfold det2
  ring

@[simp] theorem det2_swap_cols (a b c d : R) :
    det2 b a d c = -det2 a b c d := by
  unfold det2
  ring

@[simp] theorem det2_row1_add (a b a' b' c d : R) :
    det2 (a + a') (b + b') c d = det2 a b c d + det2 a' b' c d := by
  unfold det2
  ring

@[simp] theorem det2_row2_add (a b c d c' d' : R) :
    det2 a b (c + c') (d + d') = det2 a b c d + det2 a b c' d' := by
  unfold det2
  ring

@[simp] theorem det2_col1_add (a c a' c' b d : R) :
    det2 (a + a') b (c + c') d = det2 a b c d + det2 a' b c' d := by
  unfold det2
  ring

@[simp] theorem det2_col2_add (a c b d b' d' : R) :
    det2 a (b + b') c (d + d') = det2 a b c d + det2 a b' c d' := by
  unfold det2
  ring

@[simp] theorem det2_row1_smul (r a b c d : R) :
    det2 (r * a) (r * b) c d = r * det2 a b c d := by
  unfold det2
  ring

@[simp] theorem det2_row2_smul (r a b c d : R) :
    det2 a b (r * c) (r * d) = r * det2 a b c d := by
  unfold det2
  ring

@[simp] theorem det2_col1_smul (r a b c d : R) :
    det2 (r * a) b (r * c) d = r * det2 a b c d := by
  unfold det2
  ring

@[simp] theorem det2_col2_smul (r a b c d : R) :
    det2 a (r * b) c (r * d) = r * det2 a b c d := by
  unfold det2
  ring

@[simp] theorem det2_upper_triangular (a b d : R) :
    det2 a b 0 d = a * d := by
  unfold det2
  ring

@[simp] theorem det2_lower_triangular (a c d : R) :
    det2 a 0 c d = a * d := by
  unfold det2
  ring

@[simp] theorem det2_mul
    (a b c d e f g h : R) :
    det2 (a * e + b * g) (a * f + b * h)
      (c * e + d * g) (c * f + d * h)
      =
    det2 a b c d * det2 e f g h := by
  unfold det2
  ring

/-- Bracket homogeneity in the left argument. -/
@[simp] theorem bracket_scale_left
    (l : R) (P Q : HomPoint2 R) :
    bracket (scale l P) Q = l * bracket P Q := by
  rcases P with ⟨x₁, y₁⟩
  rcases Q with ⟨x₂, y₂⟩
  unfold bracket scale
  ring

/-- Bracket homogeneity in the right argument. -/
@[simp] theorem bracket_scale_right
    (m : R) (P Q : HomPoint2 R) :
    bracket P (scale m Q) = m * bracket P Q := by
  rcases P with ⟨x₁, y₁⟩
  rcases Q with ⟨x₂, y₂⟩
  unfold bracket scale
  ring

/-- Bracket homogeneity under independent representative scalings. -/
@[simp] theorem bracket_scale_scale
    (l m : R) (P Q : HomPoint2 R) :
    bracket (scale l P) (scale m Q) =
      l * m * bracket P Q := by
  rcases P with ⟨x₁, y₁⟩
  rcases Q with ⟨x₂, y₂⟩
  unfold bracket scale
  ring

/--
The basic projective-linear covariance identity:

`[TP,TQ] = det(T) * [P,Q]`.
-/
@[simp] theorem bracket_lin
    (a b c d : R) (P Q : HomPoint2 R) :
    bracket (lin a b c d P) (lin a b c d Q) =
      det2 a b c d * bracket P Q := by
  rcases P with ⟨x₁, y₁⟩
  rcases Q with ⟨x₂, y₂⟩
  unfold bracket lin det2
  ring

/-- Cross-ratio numerator in homogeneous bracket form. -/
def crossNum
    (P₁ P₂ P₃ P₄ : HomPoint2 R) : R :=
  bracket P₁ P₃ * bracket P₂ P₄

/-- Cross-ratio denominator in homogeneous bracket form. -/
def crossDen
    (P₁ P₂ P₃ P₄ : HomPoint2 R) : R :=
  bracket P₁ P₄ * bracket P₂ P₃

/--
Scaling four homogeneous representatives scales the cross-ratio numerator by
the product of the four scale factors.
-/
theorem crossNum_scale
    (l₁ l₂ l₃ l₄ : R)
    (P₁ P₂ P₃ P₄ : HomPoint2 R) :
    crossNum
        (scale l₁ P₁) (scale l₂ P₂)
        (scale l₃ P₃) (scale l₄ P₄)
      =
    (l₁ * l₂ * l₃ * l₄) * crossNum P₁ P₂ P₃ P₄ := by
  unfold crossNum
  rw [bracket_scale_scale l₁ l₃ P₁ P₃]
  rw [bracket_scale_scale l₂ l₄ P₂ P₄]
  ring

/--
Scaling four homogeneous representatives scales the cross-ratio denominator by
the same product of the four scale factors.
-/
theorem crossDen_scale
    (l₁ l₂ l₃ l₄ : R)
    (P₁ P₂ P₃ P₄ : HomPoint2 R) :
    crossDen
        (scale l₁ P₁) (scale l₂ P₂)
        (scale l₃ P₃) (scale l₄ P₄)
      =
    (l₁ * l₂ * l₃ * l₄) * crossDen P₁ P₂ P₃ P₄ := by
  unfold crossDen
  rw [bracket_scale_scale l₁ l₄ P₁ P₄]
  rw [bracket_scale_scale l₂ l₃ P₂ P₃]
  ring

/--
Representative-independence of the cross-ratio in cross-multiplied form.

This avoids division and therefore works over any commutative ring.
-/
theorem crossRatio_scale_cross_mul
    (l₁ l₂ l₃ l₄ : R)
    (P₁ P₂ P₃ P₄ : HomPoint2 R) :
    crossNum
        (scale l₁ P₁) (scale l₂ P₂)
        (scale l₃ P₃) (scale l₄ P₄) *
      crossDen P₁ P₂ P₃ P₄
      =
    crossNum P₁ P₂ P₃ P₄ *
      crossDen
        (scale l₁ P₁) (scale l₂ P₂)
        (scale l₃ P₃) (scale l₄ P₄) := by
  rw [crossNum_scale, crossDen_scale]
  ring

/--
A linear transformation scales the cross-ratio numerator by `det(T)^2`.
-/
theorem crossNum_lin
    (a b c d : R)
    (P₁ P₂ P₃ P₄ : HomPoint2 R) :
    crossNum
        (lin a b c d P₁) (lin a b c d P₂)
        (lin a b c d P₃) (lin a b c d P₄)
      =
    (det2 a b c d) ^ 2 * crossNum P₁ P₂ P₃ P₄ := by
  unfold crossNum
  rw [bracket_lin a b c d P₁ P₃]
  rw [bracket_lin a b c d P₂ P₄]
  ring

/--
A linear transformation scales the cross-ratio denominator by `det(T)^2`.
-/
theorem crossDen_lin
    (a b c d : R)
    (P₁ P₂ P₃ P₄ : HomPoint2 R) :
    crossDen
        (lin a b c d P₁) (lin a b c d P₂)
        (lin a b c d P₃) (lin a b c d P₄)
      =
    (det2 a b c d) ^ 2 * crossDen P₁ P₂ P₃ P₄ := by
  unfold crossDen
  rw [bracket_lin a b c d P₁ P₄]
  rw [bracket_lin a b c d P₂ P₃]
  ring

/--
Projective-line cross-ratio invariance in cross-multiplied form.

This is the algebraic invariant behind the Klein/Erlangen projective-line
cross-ratio theorem, expressed without division.
-/
theorem crossRatio_lin_cross_mul
    (a b c d : R)
    (P₁ P₂ P₃ P₄ : HomPoint2 R) :
    crossNum
        (lin a b c d P₁) (lin a b c d P₂)
        (lin a b c d P₃) (lin a b c d P₄) *
      crossDen P₁ P₂ P₃ P₄
      =
    crossNum P₁ P₂ P₃ P₄ *
      crossDen
        (lin a b c d P₁) (lin a b c d P₂)
        (lin a b c d P₃) (lin a b c d P₄) := by
  rw [crossNum_lin, crossDen_lin]
  ring

end HomPoint2

end InfoGeometry.Projective.KleinCrossRatioInvariant
