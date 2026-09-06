import Mathlib.Tactic
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Arithmetic.PrimeGrandCanonicalSouriauSymmetry

Finite symmetry labels for the zeta-plane duality package.

This file records the reflection/conjugation generators without claiming an
analytic continuation theorem.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeGrandCanonicalSouriauSymmetry

/-- The critical line `Re(s) = 1/2`. -/
def CriticalLine (s : ℂ) : Prop :=
  s.re = (1 : ℝ) / 2

/-- Finite symmetry labels for the zeta-plane duality package. -/
inductive ZetaPlaneSymmetry where
  | id
  | functionalEquation
  | conjugation
  | functionalConjugation

/-- Action of the finite zeta-plane symmetry labels. -/
def zetaPlaneAct : ZetaPlaneSymmetry → ℂ → ℂ
  | ZetaPlaneSymmetry.id, s => s
  | ZetaPlaneSymmetry.functionalEquation, s => 1 - s
  | ZetaPlaneSymmetry.conjugation, s => star s
  | ZetaPlaneSymmetry.functionalConjugation, s => 1 - star s

@[simp] theorem zetaPlaneAct_involutive (g : ZetaPlaneSymmetry) (s : ℂ) :
    zetaPlaneAct g (zetaPlaneAct g s) = s := by
  cases g <;> simp [zetaPlaneAct]

/-- Critical line preserved by the finite symmetry package. -/
theorem zetaPlaneAct_preserves_criticalLine
    (g : ZetaPlaneSymmetry) {s : ℂ}
    (hs : CriticalLine s) :
    CriticalLine (zetaPlaneAct g s) := by
  cases g <;> simp [zetaPlaneAct, CriticalLine] at *
  · exact hs
  · linarith [hs]
  · exact hs
  · linarith [hs]

end InfoGeometry.Arithmetic.PrimeGrandCanonicalSouriauSymmetry
