import InfoGeometry.Projective.PuncturedAffineLogDifferential

/-!
# Laurent inversion and the logarithmic Euler derivation

The Laurent-algebra involution `T ↦ T⁻¹` reverses the Euler/logarithmic
derivation.  This is the finite algebraic Klein relation; no analytic branch
of `log` is introduced here.
-/

namespace InfoGeometry.Projective.PuncturedAffineKleinInversionBridge

open scoped LaurentPolynomial
open InfoGeometry.Projective.PuncturedAffineLogDifferential

abbrev LaurentRing := LaurentPolynomial ℂ

noncomputable def inversion : LaurentRing ≃ₐ[ℂ] LaurentRing := LaurentPolynomial.invert

@[simp] theorem inversion_T (n : ℤ) :
    inversion (LaurentPolynomial.T n) = LaurentPolynomial.T (-n) := by
  exact LaurentPolynomial.invert_T n

@[simp] theorem inversion_one : inversion (1 : LaurentRing) = 1 := by
  exact map_one inversion

theorem inversion_mul (f g : LaurentRing) :
    inversion (f * g) = inversion f * inversion g := by
  exact map_mul inversion f g

theorem inversion_involutive (f : LaurentRing) :
    inversion (inversion f) = f := by
  exact LaurentPolynomial.involutive_invert f

theorem logarithmicDifferential_inversion_anticommute (f : LaurentRing) :
    logarithmicDifferential (inversion f) =
      -(inversion (logarithmicDifferential f)) := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg =>
      simp only [map_add, hf, hg, neg_add]
  | C_mul_T n c =>
      simp [inversion, logarithmicDifferential_C_mul_T, Algebra.smul_def]

end InfoGeometry.Projective.PuncturedAffineKleinInversionBridge
