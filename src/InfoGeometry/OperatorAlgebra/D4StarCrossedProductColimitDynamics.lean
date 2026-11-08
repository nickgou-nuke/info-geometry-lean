import InfoGeometry.OperatorAlgebra.D4StarCrossedProductTopologicalColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.D4StarColimitDynamics

/-!
# Topological dynamics on a crossed-product colimit diagram

This bridge adds only stagewise continuous discrete dynamics to the existing
`TopCat` crossed-product diagram.  The generic colimit descent then produces a
genuine colimit flow.  No algebraic direct-limit identification, KMS claim,
or crossed-product universal property is inferred from the topological
carrier.
-/

namespace InfoGeometry.OperatorAlgebra.D4StarCrossedProductColimitDynamics

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct
open InfoGeometry.OperatorAlgebra.D4StarCrossedProductTopologicalColimit
open InfoGeometry.OperatorAlgebra.D4StarCrossedProductTopologicalTransitions
open InfoGeometry.Topology.ContinuousQuotientDescent
open InfoGeometry.Topology.ColimitDynamics

noncomputable section

variable {I : Type*} [Preorder I]

structure ContinuousD4StarCrossedProductFlowSystem
    (T : ContinuousD4StarCrossedProductTransitionSystem I) where
  stageFlow : I → ℤ →
    (TopCat.of D4StarCrossedProduct ⟶ TopCat.of D4StarCrossedProduct)
  flow_zero : ∀ i, stageFlow i 0 = 𝟙 (TopCat.of D4StarCrossedProduct)
  flow_add : ∀ i (s t : ℤ),
    stageFlow i (s + t) = stageFlow i t ≫ stageFlow i s
  flow_natural : ∀ {i j : I} (hij : i ≤ j) (t : ℤ),
    stageFlow i t ≫ T.transitionTopCatHom hij =
      T.transitionTopCatHom hij ≫ stageFlow j t

variable {T : ContinuousD4StarCrossedProductTransitionSystem I}
variable (F : ContinuousD4StarCrossedProductFlowSystem T)

def toTopologicalFlowSystem : TopologicalDiscreteFlowSystem (J := I) where
  carrier := topologicalDiagram T
  flow := F.stageFlow
  flow_zero := F.flow_zero
  flow_add := F.flow_add
  flow_natural := by
    intro _ j f t
    exact F.flow_natural (leOfHom f) t

variable (C : Cocone (topologicalDiagram T))
variable (hC : IsColimit C)

noncomputable def colimitEndomorphism (t : ℤ) : C.pt ⟶ C.pt :=
  InfoGeometry.Topology.ColimitDynamics.colimitEndomorphism
    (toTopologicalFlowSystem F) C hC t

@[simp] theorem colimitEndomorphism_ι (i : I) (t : ℤ) :
    C.ι.app i ≫ colimitEndomorphism F C hC t =
      F.stageFlow i t ≫ C.ι.app i := by
  exact InfoGeometry.Topology.ColimitDynamics.colimitEndomorphism_ι
    (toTopologicalFlowSystem F) C hC i t

theorem colimitEndomorphism_zero :
    colimitEndomorphism F C hC 0 = 𝟙 C.pt := by
  exact InfoGeometry.Topology.ColimitDynamics.colimitEndomorphism_zero
    (toTopologicalFlowSystem F) C hC

theorem colimitEndomorphism_add (s t : ℤ) :
    colimitEndomorphism F C hC (s + t) =
      colimitEndomorphism F C hC t ≫
        colimitEndomorphism F C hC s := by
  exact InfoGeometry.Topology.ColimitDynamics.colimitEndomorphism_add
    (toTopologicalFlowSystem F) C hC s t

noncomputable def colimitFlow : ContinuousFlow C.pt where
  flow := fun t => colimitEndomorphism F C hC t
  zero_law := by
    intro x
    have h := congrArg (fun f : C.pt ⟶ C.pt => f x)
      (colimitEndomorphism_zero (F := F) (C := C) (hC := hC))
    exact h
  add_law := by
    intro s t x
    have h := congrArg (fun f : C.pt ⟶ C.pt => f x)
      (colimitEndomorphism_add (F := F) (C := C) (hC := hC) s t)
    exact h
  continuous := by
    intro t
    exact (colimitEndomorphism F C hC t).hom.continuous

@[simp] theorem colimitFlow_apply (t : ℤ) :
    (colimitFlow F C hC).flow t = colimitEndomorphism F C hC t :=
  rfl

end

end InfoGeometry.OperatorAlgebra.D4StarCrossedProductColimitDynamics
