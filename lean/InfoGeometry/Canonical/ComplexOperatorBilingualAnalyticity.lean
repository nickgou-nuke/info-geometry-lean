/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SouriauOnsagerBKMHestenesAnalyticColimit
import InfoGeometry.OperatorAlgebra.ComplexTimeCorrelation
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Operator-valued complex and phase-form analyticity

The phase structure and its complex-linear-map theorem are reused from the
existing Hestenes colimit owner.  The target remains an arbitrary complex
normed module, in particular the actual noncommutative represented C⋆ algebra.

The Cauchy one-form is calibrated to the function as `ω_F(z,v) = v • F(z)`.
Its planar exterior derivative is computed from the actual real Fréchet
derivatives.  No unrelated closed form or integral backend is supplied.
-/

noncomputable section

namespace InfoGeometry.Canonical.ComplexOperatorBilingualAnalyticity

open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Canonical.SouriauOnsagerBKMHestenesAnalyticColimit
open InfoGeometry.OperatorAlgebra.ComplexTimeConjugation
open InfoGeometry.OperatorAlgebra.ComplexTimeCorrelation

section PhaseDerivative

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Analyticity supplies the actual derivative; complex linearity supplies
the real phase-form Cauchy--Riemann law on arbitrary operator targets. -/
def analyticAtToPhaseCauchy {f : E → F} {x : E} (hf : AnalyticAt ℂ f x) :
    CauchyAnalyticAt (complexModulePhase E) (complexModulePhase F) f x where
  deriv := (fderiv ℂ f x).restrictScalars ℝ
  has_fderiv_at := hf.differentiableAt.hasFDerivAt.restrictScalars ℝ
  phase_linear_deriv := complexLinearMap_isPhaseLinear (fderiv ℂ f x)

end PhaseDerivative

section CalibratedForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The canonical function-to-form calibration for one complex parameter. -/
def complexCauchyCalibration : HestenesFormCalibration ℂ ℂ E where
  formOf f := fun z v => v • f z

/-- The oriented planar exterior derivative, using the two real directions
`1` and `I` on the parameter plane. -/
def planarExteriorDerivative (ω : OperatorOneForm ℂ ℂ E) (z : ℂ) : E :=
  fderiv ℝ (fun w => ω w Complex.I) z 1 -
    fderiv ℝ (fun w => ω w 1) z Complex.I

/-- The calibrated form is closed because of the actual derivative's phase
law.  This is a differential assertion, with no implicit integration claim. -/
theorem calibratedForm_closed_of_phaseCauchy
    {f : ℂ → E} {z : ℂ}
    (hf : CauchyAnalyticAt (complexModulePhase ℂ) (complexModulePhase E) f z) :
    planarExteriorDerivative (complexCauchyCalibration.formOf f) z = 0 := by
  have hi : HasFDerivAt (fun w => Complex.I • f w) (Complex.I • hf.deriv) z :=
    hf.has_fderiv_at.const_smul Complex.I
  have h1 : HasFDerivAt (fun w => (1 : ℂ) • f w) hf.deriv z := by
    simpa only [one_smul] using hf.has_fderiv_at
  have hcr : hf.deriv Complex.I = Complex.I • hf.deriv 1 := by
    simpa [complexModulePhase, complexModuleAxis] using hf.cauchyRiemann_apply (1 : ℂ)
  change fderiv ℝ (fun w => Complex.I • f w) z 1 -
    fderiv ℝ (fun w => (1 : ℂ) • f w) z Complex.I = 0
  rw [hi.fderiv, h1.fderiv]
  change Complex.I • hf.deriv 1 - hf.deriv Complex.I = 0
  exact sub_eq_zero.mpr hcr.symm

theorem calibratedForm_closed_of_analyticAt {f : ℂ → E} {z : ℂ}
    (hf : AnalyticAt ℂ f z) :
    planarExteriorDerivative (complexCauchyCalibration.formOf f) z = 0 :=
  calibratedForm_closed_of_phaseCauchy (analyticAtToPhaseCauchy hf)

end CalibratedForm

section OperatorOrbit

variable {C : Type*} [CStarAlgebra C]

/-- The calibrated Cauchy form uses the actual algebra product with the
central parameter differential.  The observable values remain operators. -/
theorem calibratedForm_eq_leftCauchyForm (f : ℂ → C) :
    complexCauchyCalibration.formOf f =
      leftCauchyForm f (fun a v => a * algebraMap ℂ C v) := by
  funext z v
  change v • f z = f z * algebraMap ℂ C v
  rw [Algebra.smul_def, Algebra.commutes]

def alphaPhaseCauchy (G B : C) (z : ℂ) :
    CauchyAnalyticAt (complexModulePhase ℂ) (complexModulePhase C)
      (fun w => alpha G w B) z :=
  analyticAtToPhaseCauchy (alpha_analyticAt G B z)

/-- Operator-valued Cauchy--Riemann law for the full complex-time orbit. -/
theorem alpha_realDerivative_phase (G B : C) (z v : ℂ) :
    (alphaPhaseCauchy G B z).deriv (Complex.I * v) =
      Complex.I • (alphaPhaseCauchy G B z).deriv v := by
  simpa [complexModulePhase, complexModuleAxis, smul_eq_mul] using
    (alphaPhaseCauchy G B z).cauchyRiemann_apply v

theorem alpha_calibratedForm_closed (G B : C) (z : ℂ) :
    planarExteriorDerivative
      (complexCauchyCalibration.formOf (fun w => alpha G w B)) z = 0 :=
  calibratedForm_closed_of_phaseCauchy (alphaPhaseCauchy G B z)

/-- Correlation readout inherits the same calibrated differential law from
the proved operator orbit, via its continuous-linear state functional. -/
theorem correlation_calibratedForm_closed
    (φ : C →L[ℂ] ℂ) (G A B : C) (z : ℂ) :
    planarExteriorDerivative
      (complexCauchyCalibration.formOf (correlation φ G A B)) z = 0 :=
  calibratedForm_closed_of_analyticAt (correlation_analyticAt φ G A B z)

end OperatorOrbit

end InfoGeometry.Canonical.ComplexOperatorBilingualAnalyticity
