/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealDualTwistor
import InfoGeometry.Twistor.RealTwistorGlideHolonomy

/-!
# The glide on a real twistor and its genuine dual

The chosen deck-fiber representation acts on covectors contragrediently by
precomposition with the inverse twistor map. It preserves the existing
neutral and symplectic forms and the incident constraint. Its square translates
the base and negates both the primal twistor and its actual algebraic dual.
This constructs a chosen deck representation. The companion algebraic Pin
lift of the Clifford vector action is not identified with a representation on
this twistor fibre; no associated-bundle quotient is constructed. No inner
product or self-duality of the bare twistor carrier is imposed.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealTwistorGlideDual

open InfoGeometry.Topology.KleinQuotientDeckInvariants
open RealDualTwistor RealTwistorBlockInversion RealTwistorGlideHolonomy

abbrev DualTwistorSpace := RealDualTwistor.Carrier TwistorSpace

section FrameFunctor

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The contragredient lift preserves the identity frame. -/
theorem frameAction_one : frameAction (1 : V ≃ₗ[ℝ] V) = 1 := by
  apply LinearEquiv.ext
  intro p
  apply Prod.ext
  · rfl
  · apply LinearMap.ext
    intro v
    rfl

/-- Inverse precomposition has the required order for a frame action. -/
theorem frameAction_mul (e f : V ≃ₗ[ℝ] V) :
    frameAction (e * f) = frameAction e * frameAction f := by
  apply LinearEquiv.ext
  intro p
  apply Prod.ext
  · rfl
  · apply LinearMap.ext
    intro v
    rfl

end FrameFunctor

/-- Actual contragredient action on `TwistorSpace × Module.Dual ℝ TwistorSpace`. -/
def dualHolonomy (g : KleinDeckGroup) : DualTwistorSpace ≃ₗ[ℝ] DualTwistorSpace :=
  frameAction (spinHolonomy g)

@[simp] theorem dualHolonomy_one : dualHolonomy KleinDeckGroup.one = 1 := by
  simp only [dualHolonomy, spinHolonomy_one, frameAction_one]

theorem dualHolonomy_mul (g h : KleinDeckGroup) :
    dualHolonomy (KleinDeckGroup.mul g h) = dualHolonomy g * dualHolonomy h := by
  simp only [dualHolonomy, spinHolonomy_mul, frameAction_mul]

/-- Full base-plus-dual action, retaining the affine deck translation. -/
def totalDualAction (g : KleinDeckGroup) (s : PlanePoint × DualTwistorSpace) :
    PlanePoint × DualTwistorSpace :=
  (deckAction g s.1, dualHolonomy g s.2)

@[simp] theorem totalDualAction_one (s : PlanePoint × DualTwistorSpace) :
    totalDualAction KleinDeckGroup.one s = s := by
  simp [totalDualAction, dualHolonomy_one, deckAction_one]

theorem totalDualAction_mul (g h : KleinDeckGroup) (s : PlanePoint × DualTwistorSpace) :
    totalDualAction (KleinDeckGroup.mul g h) s =
      totalDualAction g (totalDualAction h s) := by
  simp only [totalDualAction, deckAction_mul, dualHolonomy_mul, LinearEquiv.mul_apply]

/-- Forgetting the covector recovers the already-defined total twistor action. -/
theorem totalDualAction_primal (g : KleinDeckGroup) (s : PlanePoint × DualTwistorSpace) :
    ((totalDualAction g s).1, (totalDualAction g s).2.1) =
      totalSpinAction g (s.1, s.2.1) := rfl

def totalDualGlide (s : PlanePoint × DualTwistorSpace) : PlanePoint × DualTwistorSpace :=
  totalDualAction KleinDeckGroup.b s

@[simp] theorem totalDualGlide_apply (s : PlanePoint × DualTwistorSpace) :
    totalDualGlide s = (deckB s.1, frameAction blockRotation s.2) := by
  simp [totalDualGlide, totalDualAction, dualHolonomy, spinHolonomy,
    KleinDeckGroup.b, deckAction, deckB, signR, signZ]

/-- The dual minus sign is proved by evaluation on every twistor. -/
theorem frameAction_blockRotation_sq (p : DualTwistorSpace) :
    frameAction blockRotation (frameAction blockRotation p) = (-p.1, -p.2) := by
  apply Prod.ext
  · exact blockRotation_sq p.1
  · apply LinearMap.ext
    intro w
    change p.2 (-w) = -(p.2 w)
    exact map_neg p.2 w

theorem totalDualGlide_sq (s : PlanePoint × DualTwistorSpace) :
    totalDualGlide (totalDualGlide s) =
      ((s.1.1, s.1.2 + 2), (-s.2.1, -s.2.2)) := by
  simp only [totalDualGlide_apply, deckB_sq, frameAction_blockRotation_sq]

theorem totalDualGlide_no_fixed (s : PlanePoint × DualTwistorSpace) :
    totalDualGlide s ≠ s := by
  simpa only [totalDualGlide_apply] using
    glideFiber_no_fixed (frameAction blockRotation) s

/-- The neutral evaluation form is preserved on the actual total-action fibers. -/
theorem totalDualAction_neutral (g : KleinDeckGroup)
    (s t : PlanePoint × DualTwistorSpace) :
    neutralForm (totalDualAction g s).2 (totalDualAction g t).2 =
      neutralForm s.2 t.2 :=
  neutralForm_frameAction (spinHolonomy g) s.2 t.2

/-- The canonical symplectic form is preserved by the same contragredient action. -/
theorem totalDualAction_symplectic (g : KleinDeckGroup)
    (s t : PlanePoint × DualTwistorSpace) :
    symplecticForm (totalDualAction g s).2 (totalDualAction g t).2 =
      symplecticForm s.2 t.2 :=
  symplecticForm_frameAction (spinHolonomy g) s.2 t.2

/-- The actual evaluation constraint is invariant in both directions. -/
theorem totalDualAction_incident (g : KleinDeckGroup) (s : PlanePoint × DualTwistorSpace) :
    Incident (totalDualAction g s).2 ↔ Incident s.2 :=
  incident_frameAction (spinHolonomy g) s.2

end InfoGeometry.Twistor.RealTwistorGlideDual
