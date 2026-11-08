import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.AmariZetaDuallyFlatGeometry
import InfoGeometry.Canonical.PrimonColimitAlgebra

/-!
# Conditional spectral confinement

This owner isolates the elementary complex-algebra consequence used by the
proposed confinement argument.  It does not assert that a zeta zero supplies
the variance hypotheses, and therefore does not claim the Riemann hypothesis.
Those analytic/physical hypotheses remain an explicit interface.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.SpectralActionConfinement

open Complex
open InfoGeometry.Arithmetic.AmariZeta
open InfoGeometry.Canonical.PrimonColimitAlgebra
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation

/-! ## Algebraic colimit readout

The repository's matrix tower is complex-linear.  The following names expose
that existing descended trace to this arithmetic owner without changing its
carrier or pretending that it is an analytic spectral trace.
-/

abbrev PrimonUHFAlgebra := PrimonCarrier

noncomputable def colimitTrace : PrimonUHFAlgebra →ₗ[ℂ] ℂ :=
  primonTrace

@[simp] theorem colimitTrace_stage (n : ℕ) (A : PrimonStage n) :
    colimitTrace (stageInjection n A) = matrixTraceState n A := by
  exact primonTrace_stage n A

theorem colimitTrace_cyclic (x y : PrimonUHFAlgebra) :
    colimitTrace (x * y) = colimitTrace (y * x) := by
  exact primonTrace_cyclic x y

theorem colimitTrace_positive (x : PrimonUHFAlgebra) :
    0 ≤ (colimitTrace (star x * x)).re := by
  exact primonTrace_positive x

/-- The quadratic Fisher/Casimir expression attached to a complex parameter. -/
def spectralVariance (s : ℂ) : ℂ := s * (1 - s)

@[simp] theorem spectralVariance_eq_fisherRaoMetric (s : ℂ) :
    spectralVariance s = fisherRaoMetric s := rfl

theorem spectralVariance_im_eq
    (s : ℂ) :
    (spectralVariance s).im = s.im * (1 - 2 * s.re) := by
  simp [spectralVariance, mul_im]
  ring

theorem spectralVariance_re_of_im_zero
    {s : ℂ} (him : s.im = 0) :
    (spectralVariance s).re = s.re * (1 - s.re) := by
  simp [spectralVariance, him, mul_re]

/-! The honest algebraic replacement for the proposed axiom-driven theorem. -/
theorem real_variance_bound_implies_re_half
    {s : ℂ}
    (hreal : (spectralVariance s).im = 0)
    (hbound : (1 / 4 : ℝ) ≤ (spectralVariance s).re) :
    s.re = 1 / 2 := by
  rcases (fisherRaoMetric_is_real_iff s).mp hreal with hline | him
  · exact hline
  · rw [spectralVariance_re_of_im_zero him] at hbound
    nlinarith [sq_nonneg (s.re - 1 / 2)]

/-- Explicit hypotheses for any future analytic or physical realization. -/
/- The variance hypotheses are supplied directly to the theorem below. -/

theorem confinement_of_physicalVarianceEvidence
    {s : ℂ}
    (hreal : (spectralVariance s).im = 0)
    (hbound : (1 / 4 : ℝ) ≤ (spectralVariance s).re) :
    s.re = 1 / 2 := by
  exact real_variance_bound_implies_re_half hreal hbound

end InfoGeometry.Arithmetic.SpectralActionConfinement
