import InfoGeometry.Topology.CompletedZetaPotentialAndRealGibbsFisherBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ActualXiSymmetryDatumBridge

/-!
# Concrete completed-Xi datum

This file connects the abstract modulus-symmetry datum to Mathlib's concrete
`riemannXi`.  The functional equation and Schwarz reflection are consumed from
their existing owners; no Hardy-Z factorization, Riemann-hypothesis statement,
or analytic continuation theorem is introduced here.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualCompletedXiDatumBridge

open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Arithmetic.ActualRiemannXiSchwarzBridge
open InfoGeometry.Topology.CompletedZetaPotentialAndRealGibbsFisherBridge
open InfoGeometry.Canonical.ActualXiSymmetryDatumBridge

/-- The abstract completed-Xi datum realized by Mathlib's concrete `riemannXi`. -/
def actualCompletedXiDatum_concrete :
    CompletedXiDatum riemannXi :=
  InfoGeometry.Topology.CompletedZetaPotentialAndRealGibbsFisherBridge.actualCompletedXiDatum_unconditional

@[simp] theorem actualCompletedXiDatum_concrete_func_eq (s : ℂ) :
    riemannXi (1 - s) = riemannXi s := by
  exact riemannXi_one_sub s

@[simp] theorem actualCompletedXiDatum_concrete_schwarz (s : ℂ) :
    riemannXi (star s) = star (riemannXi s) := by
  exact actualXiSchwarzHypothesis_concrete s

theorem actualCompletedXiDatum_concrete_norm_func (s : ℂ) :
    Complex.normSq (riemannXi (1 - s)) =
      Complex.normSq (riemannXi s) := by
  exact xi_norm_func riemannXi actualCompletedXiDatum_concrete s

theorem actualCompletedXiDatum_concrete_norm_schwarz (s : ℂ) :
    Complex.normSq (riemannXi (star s)) =
      Complex.normSq (riemannXi s) := by
  exact xi_norm_schwarz riemannXi actualCompletedXiDatum_concrete s

theorem actualCompletedXiDatum_concrete_zero_reflection (s : ℂ) :
    riemannXi (1 - s) = 0 ↔ riemannXi s = 0 := by
  rw [riemannXi_one_sub]

theorem actualCompletedXiDatum_concrete_zero_schwarz (s : ℂ) :
    riemannXi (star s) = 0 ↔ star (riemannXi s) = 0 := by
  rw [actualXiSchwarzHypothesis_concrete]

theorem actualCompletedXiDatum_concrete_zero_reflection_schwarz (s : ℂ) :
    riemannXi (1 - star s) = 0 ↔ riemannXi s = 0 := by
  rw [riemannXi_one_sub, actualXiSchwarzHypothesis_concrete]
  simp

theorem actualCompletedXiDatum_concrete_normSq_zero_iff (s : ℂ) :
    Complex.normSq (riemannXi s) = 0 ↔ riemannXi s = 0 := by
  exact Complex.normSq_eq_zero

theorem actualCompletedXiDatum_concrete_normSq_zero_reflection (s : ℂ) :
    Complex.normSq (riemannXi (1 - s)) = 0 ↔
      Complex.normSq (riemannXi s) = 0 := by
  rw [actualCompletedXiDatum_concrete_norm_func]

theorem actualCompletedXiDatum_concrete_normSq_zero_schwarz (s : ℂ) :
    Complex.normSq (riemannXi (star s)) = 0 ↔
      Complex.normSq (riemannXi s) = 0 := by
  rw [actualCompletedXiDatum_concrete_norm_schwarz]

end InfoGeometry.Canonical.ActualCompletedXiDatumBridge
