import InfoGeometry.Canonical.ChiralZornMaxwellReadout
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# Chiral phase action on the finite Zorn readout

This owner records only the algebraic complex phase action on the chiral
vector carrier.  It does not identify the action with a differential gauge
transformation or assert a Maxwell equation.
-/

namespace InfoGeometry.Canonical.ChiralZornMaxwellGaugePhase

open InfoGeometry.Canonical.ChiralZornMaxwellReadout

abbrev ChiralVec3 := ChiralZornMaxwellReadout.ChiralVec3

noncomputable def phaseFactor (theta : ℝ) : ℂ :=
  Complex.exp (Complex.I * (theta : ℂ))

noncomputable def chiralPhase (theta : ℝ) (v : ChiralVec3) : ChiralVec3 :=
  fun i => phaseFactor theta * v i

@[simp] theorem phaseFactor_zero : phaseFactor 0 = 1 := by
  simp [phaseFactor]

theorem phaseFactor_add (theta phi : ℝ) :
    phaseFactor (theta + phi) = phaseFactor theta * phaseFactor phi := by
  unfold phaseFactor
  rw [show Complex.I * ((theta + phi : ℝ) : ℂ) =
      Complex.I * (theta : ℂ) + Complex.I * (phi : ℂ) by
    push_cast
    ring]
  exact Complex.exp_add _ _

theorem chiralPhase_zero (v : ChiralVec3) :
    chiralPhase 0 v = v := by
  funext i
  simp [chiralPhase]

theorem chiralPhase_add (theta phi : ℝ) (v : ChiralVec3) :
    chiralPhase (theta + phi) v =
      chiralPhase theta (chiralPhase phi v) := by
  funext i
  simp [chiralPhase, phaseFactor_add]
  ring

theorem chiralPhase_neg_left_inverse (theta : ℝ) (v : ChiralVec3) :
    chiralPhase (-theta) (chiralPhase theta v) = v := by
  rw [← chiralPhase_add]
  simpa using chiralPhase_zero v

end InfoGeometry.Canonical.ChiralZornMaxwellGaugePhase
