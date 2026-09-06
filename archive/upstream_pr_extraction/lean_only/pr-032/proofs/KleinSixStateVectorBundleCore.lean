import proofs.KleinGlideCoveringAtlas
import proofs.KleinSixStateBundle
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# A genuine rank-six vector-bundle core over the Klein glide quotient

The covering atlas has discrete fibre `ZMod 2`.  Every transition permutation
of this two-point fibre is a translation, hence is represented on the
six-state fibre by either the identity or the involution `Θ`.  This produces
native Mathlib `VectorBundleCore` data with locally constant transition maps.
-/

noncomputable section
namespace KleinSixStateVectorBundleCore

open Topology
open KleinBrillouinBase KleinBottleOrbitQuotient KleinGlideCovering
open KleinGlideCoveringAtlas KleinSixStateBundle TwoSheetThreeColorWeyl

abbrev Base := KleinBrillouinQuotient
abbrev State := Fin 2 × Fin 3 → ℂ

/-- An injective self-map of the two-element deck group is translation by its
value at zero. -/
theorem injective_deck2_eq_add_apply_zero (f : Deck2 → Deck2)
    (hf : Function.Injective f) (g : Deck2) :
    f g = g + f 0 := by
  have h11 : (1 + 1 : Deck2) = 0 := by decide
  fin_cases g
  · simp
  · generalize h0 : f 0 = a
    generalize h1 : f 1 = b
    fin_cases a <;> fin_cases b
    · exact False.elim (zero_ne_one (hf (h0.trans h1.symm)))
    · simp_all
    · simp_all
    · exact False.elim (zero_ne_one (hf (h0.trans h1.symm)))

/-- Deck coordinate of the transition from chart `i` to chart `j`. -/
def deckTransition (i j : Base) (x : Base) : Deck2 :=
  (coverTriv i).coordChange (coverTriv j) x 0

theorem deckTransition_self (i x : Base)
    (hx : x ∈ (coverTriv i).baseSet) :
    deckTransition i i x = 0 := by
  exact (coverTriv i).coordChange_same_apply hx 0

private theorem coordChange_injective (i j x : Base)
    (hi : x ∈ (coverTriv i).baseSet)
    (hj : x ∈ (coverTriv j).baseSet) :
    Function.Injective ((coverTriv i).coordChange (coverTriv j) x) :=
  ((coverTriv i).coordChangeHomeomorph (coverTriv j) hi hj).injective

theorem deckTransition_comp (i j k x : Base)
    (hi : x ∈ (coverTriv i).baseSet)
    (hj : x ∈ (coverTriv j).baseSet)
    (hk : x ∈ (coverTriv k).baseSet) :
    deckTransition i k x = deckTransition i j x + deckTransition j k x := by
  have hcomp := (coverTriv i).coordChange_coordChange
    (coverTriv j) (coverTriv k) hi hj (0 : Deck2)
  change (coverTriv j).coordChange (coverTriv k) x (deckTransition i j x) =
      deckTransition i k x at hcomp
  rw [injective_deck2_eq_add_apply_zero
    ((coverTriv j).coordChange (coverTriv k) x)
    (coordChange_injective j k x hj hk) (deckTransition i j x)] at hcomp
  simpa [deckTransition, add_comm] using hcomp.symm

theorem continuousOn_deckTransition (i j : Base) :
    ContinuousOn (deckTransition i j)
      ((coverTriv i).baseSet ∩ (coverTriv j).baseSet) := by
  unfold deckTransition Trivialization.coordChange
  exact continuous_snd.continuousOn.comp
    ((coverTriv j).toOpenPartialHomeomorph.continuousOn.comp
      ((coverTriv i).toOpenPartialHomeomorph.continuousOn_symm.comp
        (continuous_id.prodMk continuous_const).continuousOn
        (fun y hy ↦ (coverTriv i).mem_target.2 hy.1))
      (fun y hy ↦ by
        rw [(coverTriv j).mem_source,
          (coverTriv i).proj_symm_apply' hy.1]
        exact hy.2))
    (fun _ _ ↦ Set.mem_univ _)

/-- The continuous linear involution on states induced by `Θ`. -/
def thetaCLM : State →L[ℂ] State := theta.mulVecLin.toContinuousLinearMap

/-- The genuine `ZMod 2` fibre representation. -/
def deckFiberMap (g : Deck2) : State →L[ℂ] State :=
  if g = 0 then ContinuousLinearMap.id ℂ State else thetaCLM

@[simp] theorem deckFiberMap_zero : deckFiberMap 0 =
    ContinuousLinearMap.id ℂ State := by
  simp [deckFiberMap]

theorem deckFiberMap_add (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0)
    (g h : Deck2) (v : State) :
    deckFiberMap (g + h) v = deckFiberMap h (deckFiberMap g v) := by
  have h11 : (1 + 1 : Deck2) = 0 := by decide
  fin_cases g <;> fin_cases h
  · simp [deckFiberMap]
  · simp [deckFiberMap]
  · simp [deckFiberMap]
  · change v = theta.mulVec (theta.mulVec v)
    rw [Matrix.mulVec_mulVec, theta_sq omega homega]
    exact (Matrix.one_mulVec v).symm

theorem continuous_deckFiberMap : Continuous deckFiberMap :=
  continuous_of_discreteTopology

/-- Locally constant six-state coordinate change. -/
def stateCoordChange (i j x : Base) : State →L[ℂ] State :=
  deckFiberMap (deckTransition i j x)

theorem continuousOn_stateCoordChange (i j : Base) :
    ContinuousOn (stateCoordChange i j)
      ((coverTriv i).baseSet ∩ (coverTriv j).baseSet) :=
  continuous_deckFiberMap.comp_continuousOn
    (continuousOn_deckTransition i j)

/-- Native Mathlib rank-six vector-bundle core associated to the honest deck
involution on the six-state carrier. -/
def kleinSixStateVectorBundleCore (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    VectorBundleCore ℂ Base State Base where
  baseSet i := (coverTriv i).baseSet
  isOpen_baseSet i := (coverTriv i).open_baseSet
  indexAt x := x
  mem_baseSet_at x := mem_coverTriv_baseSet x
  coordChange := stateCoordChange
  coordChange_self i x hx v := by
    rw [stateCoordChange, deckTransition_self i x hx, deckFiberMap_zero]
    rfl
  continuousOn_coordChange := continuousOn_stateCoordChange
  coordChange_comp i j k x hx v := by
    rw [stateCoordChange, stateCoordChange, stateCoordChange,
      deckTransition_comp i j k x hx.1.1 hx.1.2 hx.2]
    exact (deckFiberMap_add omega homega _ _ v).symm

theorem vectorBundleCore_packet (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    (∀ x : Base,
      x ∈ (kleinSixStateVectorBundleCore omega homega).baseSet
        ((kleinSixStateVectorBundleCore omega homega).indexAt x)) ∧
    (∀ i x v,
      x ∈ (kleinSixStateVectorBundleCore omega homega).baseSet i →
      (kleinSixStateVectorBundleCore omega homega).coordChange i i x v = v) :=
  ⟨(kleinSixStateVectorBundleCore omega homega).mem_baseSet_at,
   fun i x v hx ↦
    (kleinSixStateVectorBundleCore omega homega).coordChange_self i x hx v⟩

end KleinSixStateVectorBundleCore
end noncomputable section
