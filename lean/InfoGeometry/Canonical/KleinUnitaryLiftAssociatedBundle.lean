import proofs.KleinVectorLiftObstruction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import proofs.KleinSixStateVectorBundleCore

/-!
# The concrete unitary lift on the six-dimensional Klein fibre

The deck transition of the existing Klein cover is lifted to the concrete
unitary generator `thetaU6`.  The full presented-group representation is
recorded separately by `concreteKleinUnitaryLift`; the theorem
`deck_generator_is_unitary_lift` identifies its `a`-generator with the local
deck transition.
-/

noncomputable section
namespace InfoGeometry.Canonical.KleinUnitaryLiftAssociatedBundle

open KleinSixStateVectorBundleCore
open KleinSixStateBundle
open KleinBrillouinBase KleinBottleOrbitQuotient KleinGlideCovering
open KleinGlideCoveringAtlas
open KleinPresentedGroup
open KleinVectorLiftObstruction
open KleinSixStateProjectiveMonodromy
open ProjectiveUnitary6

abbrev Base := KleinSixStateVectorBundleCore.Base
abbrev State6 := InfoGeometry.Algebra.FiniteSpin.Vec6C

def unitaryAction (u : U6) : State6 →L[ℂ] State6 :=
  u.1.mulVecLin.toContinuousLinearMap

def deckLiftUnit (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0)
    (g : Deck2) : U6 :=
  if g = 0 then 1 else thetaU6 omega homega

theorem thetaU6_sq (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0) :
    thetaU6 omega homega * thetaU6 omega homega = 1 := by
  apply Subtype.ext
  change reindexSix KleinSixStateBundle.theta *
      reindexSix KleinSixStateBundle.theta = 1
  rw [← map_mul, theta_sq omega homega]
  exact map_one reindexSix

theorem deckLiftUnit_add (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) (g h : Deck2) :
    deckLiftUnit omega homega (g + h) =
      deckLiftUnit omega homega h * deckLiftUnit omega homega g := by
  have h11 : (1 + 1 : Deck2) = 0 := by decide
  fin_cases g <;> fin_cases h
  · simp [deckLiftUnit]
  · simp [deckLiftUnit]
  · simp [deckLiftUnit]
  · simp [deckLiftUnit, thetaU6_sq omega homega, h11]

def deckLiftCoordChange (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0)
    (i j x : Base) : State6 →L[ℂ] State6 :=
  unitaryAction (deckLiftUnit omega homega (deckTransition i j x))

theorem continuousOn_deckLiftCoordChange (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) (i j : Base) :
    ContinuousOn (deckLiftCoordChange omega homega i j)
      ((coverTriv i).baseSet ∩ (coverTriv j).baseSet) := by
  exact (continuous_of_discreteTopology :
    Continuous (fun g : Deck2 => unitaryAction (deckLiftUnit omega homega g))).continuousOn.comp
      (continuousOn_deckTransition i j) (fun _ _ => Set.mem_univ _)

def kleinUnitaryLiftVectorBundleCore (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    VectorBundleCore ℂ Base State6 Base where
  baseSet i := (coverTriv i).baseSet
  isOpen_baseSet i := (coverTriv i).open_baseSet
  indexAt x := x
  mem_baseSet_at x := mem_coverTriv_baseSet x
  coordChange := deckLiftCoordChange omega homega
  coordChange_self i x hx v := by
    rw [deckLiftCoordChange, deckTransition_self i x hx]
    simp [unitaryAction, deckLiftUnit]
  continuousOn_coordChange := continuousOn_deckLiftCoordChange omega homega
  coordChange_comp i j k x hx v := by
    rw [deckLiftCoordChange, deckLiftCoordChange, deckLiftCoordChange,
      deckTransition_comp i j k x hx.1.1 hx.1.2 hx.2]
    change (deckLiftUnit omega homega (deckTransition j k x)).1.mulVec
        ((deckLiftUnit omega homega (deckTransition i j x)).1.mulVec v) =
      (deckLiftUnit omega homega
        (deckTransition i j x + deckTransition j k x)).1.mulVec v
    rw [deckLiftUnit_add omega homega]
    rw [Matrix.mulVec_mulVec]
    rfl

theorem deck_generator_is_unitary_lift (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    concreteKleinUnitaryLift omega homega (toKlein genA) =
      thetaU6 omega homega :=
  (concreteKleinUnitaryLift_generators omega homega).1

theorem unitary_lift_generator_packet (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    concreteKleinUnitaryLift omega homega (toKlein genA) =
        thetaU6 omega homega ∧
      concreteKleinUnitaryLift omega homega (toKlein genB) =
        liftedTrialityU6 omega homega :=
  concreteKleinUnitaryLift_generators omega homega

theorem unitary_lift_bundle_packet (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    (∀ x : Base,
      x ∈ (kleinUnitaryLiftVectorBundleCore omega homega).baseSet
        ((kleinUnitaryLiftVectorBundleCore omega homega).indexAt x)) ∧
    (∀ i x v,
      x ∈ (kleinUnitaryLiftVectorBundleCore omega homega).baseSet i →
      (kleinUnitaryLiftVectorBundleCore omega homega).coordChange i i x v = v) :=
  ⟨(kleinUnitaryLiftVectorBundleCore omega homega).mem_baseSet_at,
   fun i x v hx =>
     (kleinUnitaryLiftVectorBundleCore omega homega).coordChange_self i x hx v⟩

end InfoGeometry.Canonical.KleinUnitaryLiftAssociatedBundle
end noncomputable section
