import InfoGeometry.Projective.KleinQuadricDeRhamComplex

/-!
# A finite logarithmic differential-form carrier

This is a concrete finite-stage de Rham shadow.  The middle space has an
exact coordinate and a distinguished logarithmic coordinate.  The first
differential embeds functions into the exact coordinate, while the second
differential is zero.  The second-coordinate projection is therefore a
period functional which vanishes on exact forms and detects the logarithmic
class.

The construction is algebraic and finite.  It is not a claim about the full
smooth de Rham complex of the Klein complement.
-/

namespace InfoGeometry.Projective.KleinQuadric.FiniteDifferentialForms

noncomputable section

open InfoGeometry.Projective.KleinQuadric.DeRhamComplex
open InfoGeometry.Projective.KleinQuadric.LogDeRhamClass

abbrev Functions : Type := ℂ
abbrev OneForms : Type := ℂ × ℂ
abbrev TwoForms : Type := ℂ

/-- The exact one-form coordinate. -/
def dZero : Functions →ₗ[ℂ] OneForms where
  toFun f := (f, 0)
  map_add' f g := by ext <;> simp
  map_smul' c f := by ext <;> simp

/-- The finite carrier has no nonzero two-form obstruction. -/
def dOne : OneForms →ₗ[ℂ] TwoForms := 0

theorem differential_squared : dOne.comp dZero = 0 := by
  ext
  simp [dOne, dZero]

/-- Projection onto the logarithmic one-form coordinate. -/
def logarithmicPeriod : OneForms →ₗ[ℂ] ℂ where
  toFun ω := ω.2
  map_add' ω η := by simp
  map_smul' c ω := by simp

theorem period_vanishes_on_exact (f : Functions) :
    logarithmicPeriod (dZero f) = 0 := by
  simp [logarithmicPeriod, dZero]

def logarithmicForm (p : ℂ) : OneForms := (0, p)

theorem logarithmicForm_closed (p : ℂ) : dOne (logarithmicForm p) = 0 := by
  simp [dOne, logarithmicForm]

def cohomologyClass (p : ℂ) :
    cohomologyModule dZero dOne differential_squared :=
  closedClass dZero dOne differential_squared
    (logarithmicForm p) (logarithmicForm_closed p)

def periodOnCohomology :
    cohomologyModule dZero dOne differential_squared →ₗ[ℂ] ℂ :=
  periodClassFactor dZero dOne differential_squared
    logarithmicPeriod period_vanishes_on_exact

theorem periodOnCohomology_apply (p : ℂ) :
    periodOnCohomology (cohomologyClass p) = p := by
  exact periodClassFactor_apply dZero dOne differential_squared
    logarithmicPeriod period_vanishes_on_exact
    (logarithmicForm p) (logarithmicForm_closed p)

theorem cohomologyClass_ne_zero {p : ℂ} (hp : p ≠ 0) :
    cohomologyClass p ≠ 0 := by
  apply closedClass_ne_zero_of_period_ne_zero
    dZero dOne differential_squared (logarithmicForm p)
    (logarithmicForm_closed p) logarithmicPeriod period_vanishes_on_exact
  simpa [logarithmicPeriod, logarithmicForm] using hp

theorem exact_class_eq_zero (f : Functions) :
    closedClass dZero dOne differential_squared (dZero f)
      (exact_forms_are_closed dZero dOne differential_squared f) = 0 := by
  exact exact_form_class_eq_zero dZero dOne differential_squared f

def circleLogarithmicForm (R : ℝ) : OneForms :=
  logarithmicForm (LogDeRhamClass.logarithmicPeriod R)

theorem circleLogarithmicForm_period (R : ℝ) :
    logarithmicPeriod (circleLogarithmicForm R) =
      LogDeRhamClass.logarithmicPeriod R := by
  rfl

theorem circleLogarithmicForm_class_ne_zero (R : ℝ) (hR : 0 < R) :
    cohomologyClass (LogDeRhamClass.logarithmicPeriod R) ≠ 0 := by
  apply cohomologyClass_ne_zero
  exact LogDeRhamClass.logarithmicPeriod_ne_zero R hR

end
end InfoGeometry.Projective.KleinQuadric.FiniteDifferentialForms
