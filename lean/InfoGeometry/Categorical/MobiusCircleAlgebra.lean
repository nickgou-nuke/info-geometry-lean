import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Algebraic coefficient transport for generalized circles

This file isolates the polynomial identity behind the generalized-circle
coefficient transform under a linear fractional change of coordinates.

The variables with suffix `bar` are algebraically independent here.  A complex
specialization is obtained by taking them to be the corresponding complex
conjugates.  Keeping the statement over an arbitrary commutative ring gives a
small, robust certificate for the symbolic expansion.
-/

namespace InfoGeometry.Categorical.MobiusCircleAlgebra

open scoped ComplexConjugate

variable {R : Type*} [CommRing R]

/-- The transformed `|z|^2` coefficient. -/
def imageA (A C B Bbar a abar c cbar : R) : R :=
  A * a * abar + B * abar * c + Bbar * a * cbar + C * c * cbar

/-- The transformed constant coefficient. -/
def imageC (A C B Bbar b bbar d dbar : R) : R :=
  A * b * bbar + B * bbar * d + Bbar * b * dbar + C * d * dbar

/-- The transformed holomorphic linear coefficient. -/
def imageB (A C B Bbar _a abar b cbar d : R) : R :=
  A * abar * b + B * abar * d + Bbar * b * cbar + C * cbar * d

/-- The transformed antiholomorphic linear coefficient. -/
def imageBbar (A C B Bbar a bbar c dbar : R) : R :=
  A * a * bbar + Bbar * a * dbar + B * bbar * c + C * c * dbar

/--
The discriminant of the transformed generalized-circle coefficient matrix is
the original discriminant multiplied by the determinant norm factor.

This is the exact polynomial identity computed by the SymPy expansion:
`A' C' - B' Bbar' = (ad - bc)(abar dbar - bbar cbar)(AC - B Bbar)`.
-/
theorem image_discriminant_identity
    (A C B Bbar a abar b bbar c cbar d dbar : R) :
    imageA A C B Bbar a abar c cbar *
        imageC A C B Bbar b bbar d dbar -
      imageB A C B Bbar a abar b cbar d *
        imageBbar A C B Bbar a bbar c dbar =
      (a * d - b * c) * (abar * dbar - bbar * cbar) * (A * C - B * Bbar) := by
  unfold imageA imageC imageB imageBbar
  ring

/--
If the determinant norm factor is positive, strict negativity of the original
discriminant is transported to strict negativity of the transformed
discriminant.
-/
theorem image_discriminant_negative_of_negative
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (A C B Bbar a abar b bbar c cbar d dbar : R)
    (hdet :
      0 < (a * d - b * c) * (abar * dbar - bbar * cbar))
    (hdisc : A * C < B * Bbar) :
    imageA A C B Bbar a abar c cbar *
          imageC A C B Bbar b bbar d dbar <
        imageB A C B Bbar a abar b cbar d *
          imageBbar A C B Bbar a bbar c dbar := by
  apply sub_neg.mp
  rw [image_discriminant_identity]
  exact mul_neg_of_pos_of_neg hdet (sub_neg.mpr hdisc)

section ComplexSpecialization

open Complex

/--
A finite generalized circle in the complex plane, represented by
`A z * conj z + B * conj z + conj B * z + C = 0`.

The field `h_disc` is the nondegeneracy/real-circle condition
`A * C < |B|^2`.
-/
structure GeneralizedCircle where
  A : ℝ
  B : ℂ
  C : ℝ
  h_disc : A * C < Complex.normSq B

namespace GeneralizedCircle

/-- The transformed `|z'|^2` coefficient, specialized to complex conjugates. -/
def image_A (g : GeneralizedCircle) (a c : ℂ) : ℝ :=
  g.A * Complex.normSq a +
    (g.B * conj a * c + conj g.B * a * conj c).re +
      g.C * Complex.normSq c

/-- The transformed holomorphic linear coefficient, specialized to complex conjugates. -/
def image_B (g : GeneralizedCircle) (a b c d : ℂ) : ℂ :=
  (g.A : ℂ) * (conj a * b) + g.B * conj a * d +
    conj g.B * b * conj c + (g.C : ℂ) * (conj c * d)

/-- The transformed constant coefficient, specialized to complex conjugates. -/
def image_C (g : GeneralizedCircle) (b d : ℂ) : ℝ :=
  g.A * Complex.normSq b +
    (g.B * conj b * d + conj g.B * b * conj d).re +
      g.C * Complex.normSq d

private lemma coe_re_add_conj (w : ℂ) : ((w + conj w).re : ℂ) = w + conj w := by
  apply Complex.ext
  · simp
  · simp

private lemma image_A_eq_complex (g : GeneralizedCircle) (a c : ℂ) :
    (image_A g a c : ℂ) =
      (g.A : ℂ) * (a * conj a) + g.B * conj a * c +
        conj g.B * a * conj c + (g.C : ℂ) * (c * conj c) := by
  unfold image_A
  push_cast
  rw [← Complex.mul_conj a, ← Complex.mul_conj c]
  have h_add :
      ((g.B * conj a * c + conj (g.B * conj a * c)).re : ℂ) =
        g.B * conj a * c + conj (g.B * conj a * c) :=
    coe_re_add_conj _
  simp only [map_mul, conj_conj] at h_add
  rw [h_add]
  ring

private lemma image_C_eq_complex (g : GeneralizedCircle) (b d : ℂ) :
    (image_C g b d : ℂ) =
      (g.A : ℂ) * (b * conj b) + g.B * conj b * d +
        conj g.B * b * conj d + (g.C : ℂ) * (d * conj d) := by
  unfold image_C
  push_cast
  rw [← Complex.mul_conj b, ← Complex.mul_conj d]
  have h_add :
      ((g.B * conj b * d + conj (g.B * conj b * d)).re : ℂ) =
        g.B * conj b * d + conj (g.B * conj b * d) :=
    coe_re_add_conj _
  simp only [map_mul, conj_conj] at h_add
  rw [h_add]
  ring

/--
Complex determinant identity for the image coefficients:
`A' C' - B' conj B' = |ad - bc|^2 (AC - |B|^2)`.
-/
theorem determinant_identity (g : GeneralizedCircle) (a b c d : ℂ) :
    (image_A g a c : ℂ) * (image_C g b d : ℂ) -
        image_B g a b c d * conj (image_B g a b c d) =
      ((a * d - b * c) * conj (a * d - b * c)) *
        ((g.A : ℂ) * (g.C : ℂ) - g.B * conj g.B) := by
  rw [image_A_eq_complex, image_C_eq_complex]
  simp only [image_B, map_add, map_mul, map_sub, conj_conj, Complex.conj_ofReal]
  have h :=
    image_discriminant_identity
      (R := ℂ) (g.A : ℂ) (g.C : ℂ) g.B (conj g.B)
      a (conj a) b (conj b) c (conj c) d (conj d)
  unfold imageA imageC imageB imageBbar at h
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

/--
Real determinant identity for the image coefficients:
`A' C' - |B'|^2 = |ad - bc|^2 (AC - |B|^2)`.
-/
theorem real_determinant_identity (g : GeneralizedCircle) (a b c d : ℂ) :
    image_A g a c * image_C g b d - Complex.normSq (image_B g a b c d) =
      Complex.normSq (a * d - b * c) * (g.A * g.C - Complex.normSq g.B) := by
  apply Complex.ofReal_injective
  calc
    ((image_A g a c * image_C g b d - Complex.normSq (image_B g a b c d) : ℝ) : ℂ)
        =
          (image_A g a c : ℂ) * (image_C g b d : ℂ) -
            image_B g a b c d * conj (image_B g a b c d) := by
          push_cast
          rw [Complex.mul_conj]
    _ =
          ((a * d - b * c) * conj (a * d - b * c)) *
            ((g.A : ℂ) * (g.C : ℂ) - g.B * conj g.B) :=
          determinant_identity g a b c d
    _ =
        ((Complex.normSq (a * d - b * c) *
          (g.A * g.C - Complex.normSq g.B) : ℝ) : ℂ) := by
          push_cast
          rw [Complex.mul_conj, Complex.mul_conj]

/--
The image coefficients of a valid generalized circle under a nonsingular
linear fractional transformation again satisfy the strict discriminant
inequality.
-/
theorem image_is_generalized_circle
    (g : GeneralizedCircle) (a b c d : ℂ) (h_det : a * d - b * c ≠ 0) :
    image_A g a c * image_C g b d < Complex.normSq (image_B g a b c d) := by
  apply sub_neg.mp
  rw [real_determinant_identity]
  exact mul_neg_of_pos_of_neg
    (Complex.normSq_pos.mpr h_det)
    (sub_neg.mpr g.h_disc)

/-- The identity linear fractional transformation leaves all coefficients fixed. -/
lemma image_id (g : GeneralizedCircle) :
    image_A g 1 0 = g.A ∧ image_B g 1 0 0 1 = g.B ∧ image_C g 0 1 = g.C := by
  refine ⟨?_, ?_, ?_⟩
  · simp [image_A]
  · simp [image_B]
  · simp [image_C]

end GeneralizedCircle

end ComplexSpecialization

end InfoGeometry.Categorical.MobiusCircleAlgebra
