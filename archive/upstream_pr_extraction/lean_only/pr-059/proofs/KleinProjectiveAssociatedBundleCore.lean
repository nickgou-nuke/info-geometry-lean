import proofs.KleinProjectiveSixStateAtlas
import proofs.KleinSixStateVectorBundleCore

/-!
# The projective six-state bundle over the Klein glide quotient

The two-sheeted covering transition cocycle acts continuously on the native
topological `CP⁵` carrier.  This packages the associated projective bundle as
a Mathlib `FiberBundleCore`.
-/

noncomputable section
namespace KleinProjectiveAssociatedBundleCore

open Topology
open KleinBrillouinBase KleinBottleOrbitQuotient KleinGlideCovering
open KleinGlideCoveringAtlas KleinSixStateBundle TwoSheetThreeColorWeyl
open KleinProjectiveSixState KleinProjectiveSixStateAtlas
open KleinSixStateVectorBundleCore

abbrev Base := KleinBrillouinQuotient
abbrev ProjectiveState := KleinProjectiveSixState.ProjectiveSixState

theorem thetaOnNonzero_continuous (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    Continuous (thetaOnNonzero omega homega) := by
  apply Continuous.subtype_mk
  exact thetaCLM.continuous.comp continuous_subtype_val

theorem projectiveTheta_continuous (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    Continuous (projectiveTheta omega homega) := by
  apply continuous_quot_lift
  exact continuous_quot_mk.comp (thetaOnNonzero_continuous omega homega)

/-- The honest deck action on projective states. -/
def projectiveDeckMap (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0)
    (g : Deck2) (q : ProjectiveState) : ProjectiveState :=
  if g = 0 then q else projectiveTheta omega homega q

@[simp] theorem projectiveDeckMap_zero (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) (q : ProjectiveState) :
    projectiveDeckMap omega homega 0 q = q := by
  simp [projectiveDeckMap]

theorem projectiveDeckMap_add (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0)
    (g h : Deck2) (q : ProjectiveState) :
    projectiveDeckMap omega homega (g + h) q =
      projectiveDeckMap omega homega h (projectiveDeckMap omega homega g q) := by
  have h11 : (1 + 1 : Deck2) = 0 := by native_decide
  fin_cases g <;> fin_cases h
  · simp [projectiveDeckMap]
  · simp [projectiveDeckMap]
  · simp [projectiveDeckMap]
  · exact (projectiveTheta_involutive omega homega q).symm

theorem continuous_projectiveDeckAction (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    Continuous (fun p : Deck2 × ProjectiveState ↦
      projectiveDeckMap omega homega p.1 p.2) := by
  rw [continuous_prod_of_discrete_left]
  intro g
  fin_cases g
  · simpa [projectiveDeckMap] using
      (continuous_id : Continuous (id : ProjectiveState → ProjectiveState))
  · simpa [projectiveDeckMap] using projectiveTheta_continuous omega homega

def projectiveCoordChange (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0)
    (i j x : Base) (q : ProjectiveState) : ProjectiveState :=
  projectiveDeckMap omega homega (deckTransition i j x) q

theorem continuousOn_projectiveCoordChange (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) (i j : Base) :
    ContinuousOn (fun p : Base × ProjectiveState ↦
      projectiveCoordChange omega homega i j p.1 p.2)
      (((coverTriv i).baseSet ∩ (coverTriv j).baseSet) ×ˢ Set.univ) := by
  have ht : ContinuousOn
      (fun p : Base × ProjectiveState ↦ deckTransition i j p.1)
      (((coverTriv i).baseSet ∩ (coverTriv j).baseSet) ×ˢ Set.univ) :=
    (continuousOn_deckTransition i j).comp continuousOn_fst (fun _ hp ↦ hp.1)
  exact (continuous_projectiveDeckAction omega homega).comp_continuousOn
    (ht.prodMk continuousOn_snd)

/-- Native locally trivial projective `CP⁵` bundle over the Klein quotient. -/
def kleinProjectiveFiberBundleCore (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    FiberBundleCore Base Base ProjectiveState where
  baseSet i := (coverTriv i).baseSet
  isOpen_baseSet i := (coverTriv i).open_baseSet
  indexAt x := x
  mem_baseSet_at x := mem_coverTriv_baseSet x
  coordChange := projectiveCoordChange omega homega
  coordChange_self i x hx q := by
    rw [projectiveCoordChange, deckTransition_self i x hx,
      projectiveDeckMap_zero]
  continuousOn_coordChange := continuousOn_projectiveCoordChange omega homega
  coordChange_comp i j k x hx q := by
    rw [projectiveCoordChange, projectiveCoordChange, projectiveCoordChange,
      deckTransition_comp i j k x hx.1.1 hx.1.2 hx.2]
    exact (projectiveDeckMap_add omega homega _ _ q).symm

theorem projective_bundle_local_triviality (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) (b : Base) :
    b ∈ (kleinProjectiveFiberBundleCore omega homega).baseSet
      ((kleinProjectiveFiberBundleCore omega homega).indexAt b) :=
  (kleinProjectiveFiberBundleCore omega homega).mem_baseSet_at b

end KleinProjectiveAssociatedBundleCore
end noncomputable section
