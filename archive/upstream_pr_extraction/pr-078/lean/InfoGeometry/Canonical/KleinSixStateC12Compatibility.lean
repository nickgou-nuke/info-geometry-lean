import InfoGeometry.Canonical.TwelveFoldExplicitOperators
import proofs.KleinAffineDeckGroup
import proofs.KleinSixStateVectorBundleCore

/-!
# Affine Klein transport and the six-state `C₁₂` fibre action

The affine Klein generator `b` is sent to the identity fibre transport and
the glide generator `a` is sent to the order-twelve master operator.  The
Klein relation is therefore checked in the unit group itself.  This owner
does not identify the resulting affine action with the separate `ZMod 2`
vector-bundle transition map.
-/

noncomputable section
namespace InfoGeometry.Canonical.KleinSixStateC12Compatibility

open InfoGeometry.Canonical.TwelveFoldExplicitOperators
open KleinSixStateVectorBundleCore
open KleinAffineDeckGroup KleinPresentedGroup
open KleinBrillouinBase KleinBottleOrbitQuotient KleinGlideCovering KleinGlideCoveringAtlas

abbrev State := Fin 2 × Fin 3 → ℂ
abbrev StateMatrix := Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ
abbrev StateUnits := StateMatrixˣ

def masterUnit : StateUnits where
  val := masterTwelve
  inv := masterTwelve ^ 11
  val_inv := by
    rw [← pow_succ']
    exact masterTwelve_twelve
  inv_val := by
    rw [← pow_succ]
    exact masterTwelve_twelve

@[simp] theorem masterUnit_val : (masterUnit : StateMatrix) = masterTwelve := rfl

def affineC12Representation : AffineKleinGroup →* StateUnits :=
  (KleinPresentedGroup.kleinRep masterUnit 1 (by simp)).comp
    KleinAffineDeckGroup.affineKleinEquivPresented.toMonoidHom

@[simp] theorem affineC12Representation_b :
    affineC12Representation bGen = 1 := by
  simp only [affineC12Representation, MonoidHom.comp_apply]
  have hb := KleinAffineDeckGroup.affineKleinEquivPresented.right_inv
    (toKlein genB)
  have hb' : KleinAffineDeckGroup.affineKleinEquivPresented.toMonoidHom bGen =
      toKlein genB := by
    change KleinAffineDeckGroup.affineKleinEquivPresented
      (KleinAffineDeckGroup.presentedToAffine (toKlein genB)) = toKlein genB
    rw [KleinAffineDeckGroup.presentedToAffine_b]
    exact hb
  rw [hb']
  exact (kleinRep_relator_relation masterUnit 1 (by simp)).2

@[simp] theorem affineC12Representation_a :
    affineC12Representation aGen = masterUnit := by
  simp only [affineC12Representation, MonoidHom.comp_apply]
  have ha := KleinAffineDeckGroup.affineKleinEquivPresented.right_inv
    (toKlein genA)
  have ha' : KleinAffineDeckGroup.affineKleinEquivPresented.toMonoidHom aGen =
      toKlein genA := by
    change KleinAffineDeckGroup.affineKleinEquivPresented
      (KleinAffineDeckGroup.presentedToAffine (toKlein genA)) = toKlein genA
    rw [KleinAffineDeckGroup.presentedToAffine_a]
    exact ha
  rw [ha']
  exact (kleinRep_relator_relation masterUnit 1 (by simp)).1

theorem affineC12Representation_relation :
    affineC12Representation aGen * affineC12Representation bGen *
        (affineC12Representation aGen)⁻¹ =
      (affineC12Representation bGen)⁻¹ := by
  simp

def c12Action (g : AffineKleinGroup) : State →ₗ[ℂ] State :=
  (affineC12Representation g).val.mulVecLin

theorem c12Action_mul (g h : AffineKleinGroup) (v : State) :
    c12Action (g * h) v = c12Action g (c12Action h v) := by
  simp [c12Action, affineC12Representation, Matrix.mulVec_mulVec]

theorem c12Action_one (v : State) : c12Action 1 v = v := by
  simp [c12Action]

theorem c12Action_generator_packet (v : State) :
    c12Action bGen v = v ∧
    c12Action aGen v = masterTwelve.mulVec v := by
  constructor
  · rw [c12Action, affineC12Representation_b]
    simp
  · rw [c12Action, affineC12Representation_a, masterUnit_val]
    rfl

def parityUnit (g : Deck2) : StateUnits :=
  if g = 0 then 1 else masterUnit ^ 6

theorem masterUnit_twelve : masterUnit ^ 12 = 1 := by
  apply Units.ext
  exact masterTwelve_twelve

theorem parityUnit_add (g h : Deck2) :
    parityUnit (g + h) = parityUnit g * parityUnit h := by
  have h11 : (1 + 1 : Deck2) = 0 := by native_decide
  have h6 : (masterUnit ^ 6) * (masterUnit ^ 6) = 1 := by
    rw [← pow_two, ← pow_mul, show 6 * 2 = 12 by norm_num,
      masterUnit_twelve]
  fin_cases g <;> fin_cases h
  · simp [parityUnit]
  · simp [parityUnit]
  · simp [parityUnit]
  · simp [parityUnit, h6, h11]

def parityAction (g : Deck2) : State →ₗ[ℂ] State :=
  (parityUnit g).val.mulVecLin

def parityActionCLM (g : Deck2) : State →L[ℂ] State :=
  (parityAction g).toContinuousLinearMap

theorem parityAction_mul (g h : Deck2) (v : State) :
    parityAction (g + h) v = parityAction g (parityAction h v) := by
  change (parityUnit (g + h)).val.mulVec v =
    (parityUnit g).val.mulVec ((parityUnit h).val.mulVec v)
  rw [parityUnit_add, Matrix.mulVec_mulVec]
  rfl

theorem parityAction_add (g h : Deck2) (v : State) :
    parityAction (g + h) v = parityAction h (parityAction g v) := by
  have h11 : (1 + 1 : Deck2) = 0 := by native_decide
  have h6 : (masterUnit ^ 6) * (masterUnit ^ 6) = 1 := by
    rw [← pow_two, ← pow_mul, show 6 * 2 = 12 by norm_num,
      masterUnit_twelve]
  have h6m : masterTwelve ^ 6 * masterTwelve ^ 6 = (1 : StateMatrix) := by
    rw [← pow_two, ← pow_mul, show 6 * 2 = 12 by norm_num,
      masterTwelve_twelve]
  fin_cases g <;> fin_cases h <;>
    simp [parityAction, parityUnit, h6m, h11, Matrix.mulVec_mulVec]

def c12StateCoordChange (i j x : KleinSixStateVectorBundleCore.Base) : State →L[ℂ] State :=
  parityActionCLM (deckTransition i j x)

theorem continuousOn_c12StateCoordChange
    (i j : KleinSixStateVectorBundleCore.Base) :
    ContinuousOn (c12StateCoordChange i j)
      ((coverTriv i).baseSet ∩ (coverTriv j).baseSet) := by
  exact (continuous_of_discreteTopology : Continuous parityActionCLM).continuousOn.comp
    (continuousOn_deckTransition i j) (fun _ _ ↦ Set.mem_univ _)

def kleinSixStateC12VectorBundleCore
    (omega : ℂ) (_homega : omega ^ 2 + omega + 1 = 0) :
    VectorBundleCore ℂ KleinSixStateVectorBundleCore.Base State
      KleinSixStateVectorBundleCore.Base where
  baseSet i := (coverTriv i).baseSet
  isOpen_baseSet i := (coverTriv i).open_baseSet
  indexAt x := x
  mem_baseSet_at x := mem_coverTriv_baseSet x
  coordChange := c12StateCoordChange
  coordChange_self i x hx v := by
    rw [c12StateCoordChange, deckTransition_self i x hx]
    change parityActionCLM 0 v = v
    simp [parityActionCLM, parityAction, parityUnit]
  continuousOn_coordChange := continuousOn_c12StateCoordChange
  coordChange_comp i j k x hx v := by
    rw [c12StateCoordChange, c12StateCoordChange, c12StateCoordChange,
      deckTransition_comp i j k x hx.1.1 hx.1.2 hx.2]
    exact (parityAction_add _ _ v).symm

theorem c12_bundle_transition_packet
    (omega : ℂ) (_homega : omega ^ 2 + omega + 1 = 0) :
    (∀ x : KleinSixStateVectorBundleCore.Base,
      x ∈ (kleinSixStateC12VectorBundleCore omega _homega).baseSet
        ((kleinSixStateC12VectorBundleCore omega _homega).indexAt x)) ∧
    (∀ i x v,
      x ∈ (kleinSixStateC12VectorBundleCore omega _homega).baseSet i →
      (kleinSixStateC12VectorBundleCore omega _homega).coordChange i i x v = v) :=
  ⟨(kleinSixStateC12VectorBundleCore omega _homega).mem_baseSet_at,
   fun i x v hx ↦
    (kleinSixStateC12VectorBundleCore omega _homega).coordChange_self i x hx v⟩

end InfoGeometry.Canonical.KleinSixStateC12Compatibility
end noncomputable section
