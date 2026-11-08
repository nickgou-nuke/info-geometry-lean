import InfoGeometry.Krein.DiracHodgeDoubledSpace
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Massive doubled oscillator algebra

The existing doubled carrier supplies a canonical clock axis `K` with
`K² = -I`.  Scaling it by a real mass/frequency parameter gives the massive
operator `Dₘ`; the resulting statements are algebraic operator identities.
No analytic time-flow or spectral theorem is asserted here.
-/

namespace InfoGeometry.Krein.MassiveDoubledOscillator

open InfoGeometry.Krein
open InfoGeometry.Krein.DiracHodgeDoubledSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

noncomputable def massiveOperator (ω : ℝ) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  ω • clockAxis (E := E)

theorem massiveOperator_apply (ω : ℝ) (u : DoubledSpace E) :
    massiveOperator ω u = ω • clockAxis (E := E) u := by
  rfl

theorem massiveOperator_square (ω : ℝ) :
    massiveOperator ω ∘L massiveOperator ω =
      -(ω ^ 2) • ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [massiveOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply]
  rw [map_smul, smul_smul]
  rw [show clockAxis (E := E) (clockAxis (E := E) u) = -u by
    have h := congrArg (fun T : DoubledSpace E →L[ℝ] DoubledSpace E => T u)
      (K_sq_neg_id E)
    simpa [ContinuousLinearMap.comp_apply] using h]
  simp [ContinuousLinearMap.id_apply, pow_two]

theorem massiveOperator_second_order (ω : ℝ) (u : DoubledSpace E) :
    massiveOperator ω (massiveOperator ω u) = -(ω ^ 2) • u := by
  have h := congrArg (fun T : DoubledSpace E →L[ℝ] DoubledSpace E => T u)
    (massiveOperator_square (E := E) ω)
  simpa [ContinuousLinearMap.comp_apply] using h

theorem massiveOperator_first_order (ω : ℝ) (u : DoubledSpace E) :
    massiveOperator ω u = ω • clockAxis (E := E) u :=
  massiveOperator_apply ω u

end InfoGeometry.Krein.MassiveDoubledOscillator
