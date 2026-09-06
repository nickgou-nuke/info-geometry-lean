import InfoGeometry.OperatorAlgebra.D4StarCrossedProductColimitDynamics

/-!
# Observational descent for the crossed-product colimit flow

Stage observables are required to be natural for the crossed-product
transitions and invariant under the supplied stage flow.  The generic
`TopCat` colimit theorem then produces a stationary global readout.  This is
an observational factor statement only; it is not a KMS or orbifold theorem.
-/

namespace InfoGeometry.OperatorAlgebra.D4StarCrossedProductColimitObservable

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct
open InfoGeometry.OperatorAlgebra.D4StarCrossedProductTopologicalColimit
open InfoGeometry.OperatorAlgebra.D4StarCrossedProductTopologicalTransitions
open InfoGeometry.OperatorAlgebra.D4StarCrossedProductColimitDynamics
open InfoGeometry.Topology.ColimitDynamics

noncomputable section

variable {I : Type*} [Preorder I]
variable {T : ContinuousD4StarCrossedProductTransitionSystem I}
variable (F : ContinuousD4StarCrossedProductFlowSystem T)
variable (BoolCat : TopCat)

abbrev FlowInvariantObservableData : Type _ :=
  {stageObservable : ∀ i : I,
      TopCat.of D4StarCrossedProduct ⟶ BoolCat //
    (∀ {i j : I} (hij : i ≤ j),
        T.transitionTopCatHom hij ≫ stageObservable j = stageObservable i) ∧
    (∀ (i : I) (t : ℤ),
        F.stageFlow i t ≫ stageObservable i = stageObservable i)}

variable (Obs : FlowInvariantObservableData F BoolCat)

include Obs

def toGenericObservables :
    InfoGeometry.Topology.ColimitDynamics.FlowInvariantObservableData
      (toTopologicalFlowSystem F) BoolCat where
  stageObservable := {
    app := Obs.1
    naturality := by
      intro i j f
      dsimp [toTopologicalFlowSystem, topologicalDiagram]
      exact Obs.2.1 (leOfHom f)
  }
  observable_invariant := Obs.2.2

noncomputable def colimitObservable
    (C : Cocone (topologicalDiagram T))
    (hC : IsColimit C) : C.pt ⟶ BoolCat :=
  InfoGeometry.Topology.ColimitDynamics.colimitObservable
    (toTopologicalFlowSystem F) C hC BoolCat (toGenericObservables F BoolCat Obs)

@[simp] theorem colimitObservable_stage
    (C : Cocone (topologicalDiagram T))
    (hC : IsColimit C) (i : I) :
    C.ι.app i ≫ colimitObservable F BoolCat Obs C hC =
      Obs.1 i := by
  exact InfoGeometry.Topology.ColimitDynamics.colimitObservable_stage
    (toTopologicalFlowSystem F) C hC BoolCat (toGenericObservables F BoolCat Obs) i

theorem colimitObservable_invariant
    (C : Cocone (topologicalDiagram T))
    (hC : IsColimit C) (t : ℤ) :
    colimitEndomorphism F C hC t ≫
        colimitObservable F BoolCat Obs C hC =
      colimitObservable F BoolCat Obs C hC := by
  exact InfoGeometry.Topology.ColimitDynamics.colimitObservable_invariant
    (toTopologicalFlowSystem F) C hC BoolCat (toGenericObservables F BoolCat Obs) t

end

end InfoGeometry.OperatorAlgebra.D4StarCrossedProductColimitObservable
