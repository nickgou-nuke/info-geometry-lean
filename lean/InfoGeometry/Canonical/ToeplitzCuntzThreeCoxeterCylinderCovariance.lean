import InfoGeometry.Canonical.ToeplitzCuntzThreeCoxeterInnerAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.ToeplitzCuntzThreeTrialityBoundaryGroupoidColimit

/-!
# Coxeter covariance contracts for ternary cylinder projections

The inner-action owner supplies the unit `c = β₂ β₁` and its conjugation
action.  This file closes the vacuum-sector case and records the exact typed
contracts needed for the remaining finite-cylinder questions.  The
coordinatewise word action below is a quasi-free-style interface: its
covariance field is an explicit property, not a theorem derived from the
first-level inner action.  In particular, no identification of that action
with `Ad_c` on arbitrary words is asserted.  No unproved `P₁/P₂/P₃`
permutation or C*-completion is introduced here.
-/

noncomputable section

namespace InfoGeometry.Canonical.ToeplitzCuntzThreeCoxeterCylinderCovariance

open InfoGeometry.Canonical.ToeplitzCuntzThreeArtinBraidBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeCoxeterInnerAction
open InfoGeometry.Canonical.ToeplitzCuntzThreeCyclicSuperchargeBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge
open InfoGeometry.Topology.ToeplitzCuntzThreeTriality

variable {A : Type*} [Ring A] [StarRing A]
variable (g : ToeplitzCuntzThreeGenerators A)

theorem innerAction_eq_of_intertwines
    (u : Aˣ) (x y : A)
    (h : u.val * x = y * u.val) :
    u.val * x * (↑(u⁻¹) : A) = y := by
  calc
    u.val * x * (↑(u⁻¹) : A) =
        (y * u.val) * (↑(u⁻¹) : A) := by rw [h]
    _ = y * (u.val * (↑(u⁻¹) : A)) := by rw [mul_assoc]
    _ = y * 1 := by simp
    _ = y := by rw [mul_one]

theorem coxeter_conj_P0 :
    coxeterInnerAction g g.P0 = g.P0 := by
  have hright : coxeterElement g * g.P0 = g.P0 := by
    rw [coxeterElement_eq_cyclicSupercharge_add_defect]
    rw [add_mul, cyclicSupercharge_defect_annihilation_right]
    simp [defectProjection_sq]
  have hleft : g.P0 * coxeterElement g = g.P0 := by
    rw [coxeterElement_eq_cyclicSupercharge_add_defect]
    rw [mul_add, cyclicSupercharge_defect_annihilation_left]
    simp [defectProjection_sq]
  unfold coxeterInnerAction
  change coxeterElement g * g.P0 *
      (coxeterElement g * coxeterElement g) = g.P0
  rw [hright]
  calc
    g.P0 * (coxeterElement g * coxeterElement g) =
        (g.P0 * coxeterElement g) * coxeterElement g := by
          simp [mul_assoc]
    _ = g.P0 * coxeterElement g := by
      exact congrArg (fun x => x * coxeterElement g) hleft
    _ = g.P0 := hleft

theorem coxeter_conj_P1_of
    (hP1 : coxeterElement g * g.P1 = g.P3 * coxeterElement g) :
    coxeterInnerAction g g.P1 = g.P3 := by
  unfold coxeterInnerAction
  apply innerAction_eq_of_intertwines (coxeterUnit g)
  simpa using hP1

theorem coxeter_conj_P2_of
    (hP2 : coxeterElement g * g.P2 = g.P1 * coxeterElement g) :
    coxeterInnerAction g g.P2 = g.P1 := by
  unfold coxeterInnerAction
  apply innerAction_eq_of_intertwines (coxeterUnit g)
  simpa using hP2

theorem coxeter_conj_P3_of
    (hP3 : coxeterElement g * g.P3 = g.P2 * coxeterElement g) :
    coxeterInnerAction g g.P3 = g.P2 := by
  unfold coxeterInnerAction
  apply innerAction_eq_of_intertwines (coxeterUnit g)
  simpa using hP3

/-- Coordinatewise colour action on finite words.

This is the boundary/quasi-free action used by the typed contract below.  It
must not be conflated with inner conjugation by the first-level Coxeter unit:
the latter naturally transports the first letter of a cylinder and does not
automatically rotate every coordinate of an arbitrary word. -/
def coxeterWordAction (w : TernaryWord n) : TernaryWord n :=
  fun i => trialityCyclePerm (w i)

structure CoxeterCylinderProjectionData (n : ℕ) where
  projection : TernaryWord n → A
  /-- Contract for a separate coordinatewise/quasi-free action. -/
  covariance : ∀ w,
    coxeterInnerAction g (projection w) =
      projection (coxeterWordAction w)

theorem coxeter_conj_cylinderProjection
    (D : CoxeterCylinderProjectionData g n) (w : TernaryWord n) :
    coxeterInnerAction g (D.projection w) =
      D.projection (coxeterWordAction w) :=
  D.covariance w

end InfoGeometry.Canonical.ToeplitzCuntzThreeCoxeterCylinderCovariance
