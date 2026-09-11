import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Derivative of an operator conjugation curve

The theorem below is conditional on derivative data for both the unitary curve
and its star curve.  It does not assert differentiability of a modular flow.
-/

noncomputable section

namespace InfoGeometry.Canonical.GeneratorConjugationDerivative

variable {A : Type*}
variable [NormedRing A] [NormedAlgebra ℝ A] [StarRing A]

def conjugationCurve (u : ℝ → A) (x : A) (t : ℝ) : A :=
  u t * x * star (u t)

theorem hasDerivAt_conjugationCurve
    (u u' : ℝ → A) (x : A) (t : ℝ)
    (hu : HasDerivAt u (u' t) t)
    (hstar : HasDerivAt (fun s => star (u s)) (star (u' t)) t) :
    HasDerivAt (conjugationCurve u x)
      (u' t * x * star (u t) + u t * x * star (u' t)) t := by
  have hleft : HasDerivAt (fun s => u s * x) (u' t * x) t :=
    hu.mul_const x
  have hprod := hleft.mul hstar
  simpa [conjugationCurve, mul_assoc] using hprod

end InfoGeometry.Canonical.GeneratorConjugationDerivative
