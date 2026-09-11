import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.KleinQuadric
import InfoGeometry.Canonical.ComplexAnalyticBridge
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import InfoGeometry.Clifford.UniversalCoverLog

/-!
# Klein Quadric + Log-Singularity Formalization

This module packages a compact set of verifiable facts relevant to the phrase:

* Klein quadric coordinates via the Plücker form
* the logarithmic 1-form on the complement of the polar divisor: `dz / z`
* its circle integral around the singularity `z = 0`
* discrete sheet monodromy as a `2πi` increment

These are lightweight Lean lemmas intended as a stepping-stone for larger
`deRham / Chern / Wilson` developments in this codebase.
-/

namespace InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy

open Complex
open InfoGeometry.Projective.KleinQuadric
open InfoGeometry.Clifford.UniversalCoverLog

/-- Determinant-like Klein potential in Plücker coordinates. -/
noncomputable def kleinPotential : Plucker6 ℂ → ℂ := Plucker6.kleinQ

/-- Log-potential is defined on the complement of the Klein cone. -/
noncomputable def kleinLogPotential (p : Plucker6 ℂ) (_ : kleinPotential p ≠ 0) : ℂ :=
  Complex.log (kleinPotential p)

/-- The logarithmic 1-form around a pole at the origin, written as `1 / z`. -/
noncomputable def poleForm : ℂ → ℂ := fun z => (1 : ℂ) / z

/-- The canonical `2πi` circle integral of `1 / z` around the origin. -/
theorem circleIntegral_one_div (R : ℝ) (hR : 0 < R) :
    (∮ z in C((0 : ℂ), R), (poleForm z)) = (2 * Real.pi * Complex.I : ℂ) := by
  have hdiff : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) (Metric.closedBall (0 : ℂ) R) :=
    differentiableOn_const (c := (1 : ℂ))
  have hmem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by simpa [Metric.mem_ball] using hR
  have h := InfoGeometry.Canonical.ComplexAnalyticBridge.cauchyIntegralFormulaOnClosedDisc
    (c := (0 : ℂ)) (w := (0 : ℂ)) (f := fun _ : ℂ => (1 : ℂ)) hdiff hmem
  simpa [poleForm, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h

/-- `n`-winding phase from integrating the logarithmic form. -/
noncomputable def logarithmicPhase (n : ℤ) : ℂ :=
  (n : ℂ) * (2 * Real.pi * Complex.I : ℂ)

/-- Algebraic monodromy on the universal cover increments by `2πi` per sheet. -/
theorem universalCoverLog_sheet_increment (z : ℂ) (n : ℤ) :
    uLog (z, n + 1) - uLog (z, n) = (2 * Real.pi * Complex.I : ℂ) := by
  have h := uLog_deck_up (z := z) (n := n)
  calc
    uLog (z, n + 1) - uLog (z, n)
        = (uLog (z, n) + 2 * Real.pi * Complex.I) - uLog (z, n) := by
          simpa [deckUp] using congrArg (fun t => t - uLog (z, n)) h
    _ = (2 * Real.pi * Complex.I : ℂ) := by ring

/-- The corresponding phase factor for an integer number of windings is trivial.

    This is the formal statement that holonomy around the divisor is a pure phase
    with zero net multiplier after closing the loop in the multiplicative model.
-/
theorem holonomyPhase_is_root_of_unity (n : ℤ) :
    Complex.exp (logarithmicPhase n) = (1 : ℂ) := by
  simpa [logarithmicPhase] using (Complex.exp_int_mul_two_pi_mul_I n)

/-- The de Rham class induced by a loop of winding number `n`.

    It is the expected residue pairing: `n·(2πi)`. -/
theorem deRhamClass_of_winding (R : ℝ) (hR : 0 < R) (n : ℤ) :
    (n : ℂ) * (∮ z in C((0 : ℂ), R), poleForm z) = logarithmicPhase n := by
  calc
    (n : ℂ) * (∮ z in C((0 : ℂ), R), poleForm z)
        = (n : ℂ) * (2 * Real.pi * Complex.I : ℂ) := by
            rw [circleIntegral_one_div R hR]
    _ = logarithmicPhase n := rfl

/-- Wilson-loop phase for an integer winding: integrating the log-derivative form.

    This is the multiplicative holonomy around the chiral null cone boundary
    (equivalently around a small circle in the transverse plane). -/
theorem wilsonPhase_of_winding (R : ℝ) (hR : 0 < R) (n : ℤ) :
    Complex.exp ((n : ℂ) * (∮ z in C((0 : ℂ), R), poleForm z)) = (1 : ℂ) := by
  rw [deRhamClass_of_winding (R := R) hR n]
  simpa [logarithmicPhase] using (Complex.exp_int_mul_two_pi_mul_I n)

/-- Determinant/quadric classification: null (zero) determinant is equivalent to
    self-orthogonality for the Klein polar form over `ℂ`.

    This identifies the chiral null cone with the isotropic cone of the polar form. -/
theorem logDerivative_at (z : ℂ) (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (fun w : ℂ => Complex.log w) (z⁻¹) z := by
  simpa using Complex.hasDerivAt_log hz

/-- Negative branch: derivative of the local logarithmic potential for inverse scale. -/
theorem negLogDerivative_at (z : ℂ) (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (fun w : ℂ => -Complex.log w) (-z⁻¹) z := by
  simpa using (Complex.hasDerivAt_log hz).neg

/-- Determinant/quadric classification: null (zero) determinant is equivalent to
    self-orthogonality for the Klein polar form over `ℂ`.

    This identifies the chiral null cone with the isotropic cone of the polar form. -/
theorem chiralNullConductor_eq_selfOrthogonal (P : Plucker6 ℂ) :
    kleinPotential P = 0 ↔ Plucker6.polar P P = 0 := by
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hpolar : Plucker6.polar P P = (2 : ℂ) * kleinPotential P := by
    exact Plucker6.polar_self P
  constructor
  · intro hQ
    simpa [hpolar, hQ]
  · intro hPP
    have hmul : (2 : ℂ) * kleinPotential P = 0 := by
      simpa [hpolar] using hPP
    exact (mul_eq_zero.mp hmul).resolve_left h2

end InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy
