import InfoGeometry.OperatorAlgebra.D4StarCrossedProductColimitDynamics
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.D4StarColimitFlowHomeomorph

/-!
# Homeomorphisms of the crossed-product colimit flow

This file packages the invertibility of the crossed-product colimit flow as a
`Homeomorph` on the native topological carrier.  It does not assert any
additional algebraic completion or KMS structure.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.D4StarCrossedProductColimitFlowHomeomorph

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.OperatorAlgebra.D4StarCrossedProductColimitDynamics
open InfoGeometry.OperatorAlgebra.D4StarCrossedProductTopologicalColimit
open InfoGeometry.OperatorAlgebra.D4StarCrossedProductTopologicalTransitions
open InfoGeometry.Topology.ColimitDynamics

variable {I : Type*} [Preorder I]
variable {T : ContinuousD4StarCrossedProductTransitionSystem I}
variable (F : ContinuousD4StarCrossedProductFlowSystem T)
variable (C : Cocone (topologicalDiagram T))
variable (hC : IsColimit C)

/-- The homeomorphism induced by the crossed-product colimit flow. -/
noncomputable def colimitEndomorphismHomeomorph
    (t : ℤ) : C.pt ≃ₜ C.pt :=
  InfoGeometry.Topology.ColimitDynamics.colimitEndomorphismHomeomorph
    (toTopologicalFlowSystem F) C hC t

@[simp] theorem colimitEndomorphismHomeomorph_apply
    (t : ℤ) (x : C.pt) :
    colimitEndomorphismHomeomorph F C hC t x =
      colimitEndomorphism F C hC t x :=
  rfl

theorem colimitEndomorphismHomeomorph_zero_apply
    (x : C.pt) :
    colimitEndomorphismHomeomorph F C hC 0 x = x := by
  rw [colimitEndomorphismHomeomorph]
  exact InfoGeometry.Topology.ColimitDynamics.colimitEndomorphismHomeomorph_zero_apply
    (toTopologicalFlowSystem F) C hC x

theorem colimitEndomorphismHomeomorph_add_apply
    (s t : ℤ) (x : C.pt) :
    colimitEndomorphismHomeomorph F C hC (s + t) x =
      colimitEndomorphismHomeomorph F C hC s
        (colimitEndomorphismHomeomorph F C hC t x) := by
  rw [colimitEndomorphismHomeomorph]
  exact InfoGeometry.Topology.ColimitDynamics.colimitEndomorphismHomeomorph_add_apply
    (toTopologicalFlowSystem F) C hC s t x

end InfoGeometry.OperatorAlgebra.D4StarCrossedProductColimitFlowHomeomorph
