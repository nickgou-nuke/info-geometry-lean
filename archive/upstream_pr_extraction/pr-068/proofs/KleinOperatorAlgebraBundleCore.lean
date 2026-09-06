import proofs.KleinOperatorAlgebraAssociatedQuotient
import proofs.KleinSixStateVectorBundleCore

/-!
# Locally trivial operator-algebra bundle over the Klein quotient

The deck cocycle acts on `M₆(ℂ)` by the honest inner automorphism
`A ↦ Θ A Θ`.  Central phases disappear, so this construction is independent
of any projective lift of the state representation.
-/

noncomputable section
namespace KleinOperatorAlgebraBundleCore

open Topology
open KleinBrillouinBase KleinBottleOrbitQuotient KleinGlideCovering
open KleinGlideCoveringAtlas KleinSixStateVectorBundleCore
open KleinOperatorAlgebraAssociatedQuotient

abbrev Base := KleinBrillouinQuotient
abbrev Op := KleinOperatorAlgebraAssociatedQuotient.Operator

theorem operatorGlide_continuous : Continuous operatorGlide := by
  exact (continuous_const.mul continuous_id).mul continuous_const

def operatorDeckMap (g : Deck2) (A : Op) : Op :=
  if g = 0 then A else operatorGlide A

@[simp] theorem operatorDeckMap_zero (A : Op) : operatorDeckMap 0 A = A := by
  simp [operatorDeckMap]

theorem operatorDeckMap_add_group (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0)
    (g h : Deck2) (A : Op) :
    operatorDeckMap (g + h) A = operatorDeckMap h (operatorDeckMap g A) := by
  fin_cases g <;> fin_cases h
  · simp [operatorDeckMap]
  · simp [operatorDeckMap]
  · simp [operatorDeckMap]
  · exact (operatorGlide_involutive omega homega A).symm

theorem continuous_operatorDeckAction :
    Continuous (fun p : Deck2 × Op ↦ operatorDeckMap p.1 p.2) := by
  rw [continuous_prod_of_discrete_left]
  intro g
  fin_cases g
  · simpa [operatorDeckMap] using
      (continuous_id : Continuous (id : Op → Op))
  · simpa [operatorDeckMap] using operatorGlide_continuous

def operatorCoordChange (i j x : Base) (A : Op) : Op :=
  operatorDeckMap (deckTransition i j x) A

theorem continuousOn_operatorCoordChange (i j : Base) :
    ContinuousOn (fun p : Base × Op ↦ operatorCoordChange i j p.1 p.2)
      (((coverTriv i).baseSet ∩ (coverTriv j).baseSet) ×ˢ Set.univ) := by
  have ht : ContinuousOn (fun p : Base × Op ↦ deckTransition i j p.1)
      (((coverTriv i).baseSet ∩ (coverTriv j).baseSet) ×ˢ Set.univ) :=
    (continuousOn_deckTransition i j).comp continuousOn_fst (fun _ hp ↦ hp.1)
  exact continuous_operatorDeckAction.comp_continuousOn (ht.prodMk continuousOn_snd)

/-- Native locally trivial bundle with fibre the full matrix algebra. -/
def kleinOperatorAlgebraFiberBundleCore (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    FiberBundleCore Base Base Op where
  baseSet i := (coverTriv i).baseSet
  isOpen_baseSet i := (coverTriv i).open_baseSet
  indexAt x := x
  mem_baseSet_at x := mem_coverTriv_baseSet x
  coordChange := operatorCoordChange
  coordChange_self i x hx A := by
    rw [operatorCoordChange, deckTransition_self i x hx, operatorDeckMap_zero]
  continuousOn_coordChange := continuousOn_operatorCoordChange
  coordChange_comp i j k x hx A := by
    rw [operatorCoordChange, operatorCoordChange, operatorCoordChange,
      deckTransition_comp i j k x hx.1.1 hx.1.2 hx.2]
    exact (operatorDeckMap_add_group omega homega _ _ A).symm

theorem operatorCoordChange_add (i j x : Base) (A B : Op) :
    operatorCoordChange i j x (A + B) =
      operatorCoordChange i j x A + operatorCoordChange i j x B := by
  unfold operatorCoordChange operatorDeckMap
  split_ifs
  · rfl
  · exact operatorGlide_add A B

theorem operatorCoordChange_mul (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0)
    (i j x : Base) (A B : Op) :
    operatorCoordChange i j x (A * B) =
      operatorCoordChange i j x A * operatorCoordChange i j x B := by
  unfold operatorCoordChange operatorDeckMap
  split_ifs
  · rfl
  · exact operatorGlide_mul omega homega A B

theorem operatorCoordChange_one (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) (i j x : Base) :
    operatorCoordChange i j x 1 = 1 := by
  unfold operatorCoordChange operatorDeckMap
  split_ifs
  · rfl
  · exact operatorGlide_one omega homega

end KleinOperatorAlgebraBundleCore
end noncomputable section
