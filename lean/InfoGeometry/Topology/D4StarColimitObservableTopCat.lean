import InfoGeometry.Topology.D4StarColimitFlowTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology.ColimitDynamics

open CategoryTheory Limits

variable {J : Type*} [Category J]
variable (D : TopologicalDiscreteFlowSystem (J := J))
variable (C : Cocone D.carrier)
variable (hC : IsColimit C)
variable (BoolCat : TopCat)
variable (Obs : FlowInvariantObservableData D BoolCat)

/-!
# `TopCat` readout of the D₄-star colimit observable

This owner packages the verified colimit observable as a `TopCat` morphism and
records its compatibility with the descended colimit flow.
-/

noncomputable def colimitObservableTopCatHom :
    C.pt ⟶ BoolCat :=
  colimitObservable D C hC BoolCat Obs

@[simp] theorem colimitObservableTopCatHom_apply
    (x : C.pt) :
    colimitObservableTopCatHom D C hC BoolCat Obs x =
      colimitObservable D C hC BoolCat Obs x :=
  rfl

@[simp] theorem colimitObservableTopCatHom_stage (j : J) :
    C.ι.app j ≫ colimitObservableTopCatHom D C hC BoolCat Obs =
      Obs.stageObservable.app j := by
  simpa [colimitObservableTopCatHom] using
    (colimitObservable_stage D C hC BoolCat Obs j)

theorem colimitObservableTopCatHom_invariant (t : ℤ) :
    colimitEndomorphismTopCatHom D C hC t ≫
        colimitObservableTopCatHom D C hC BoolCat Obs =
      colimitObservableTopCatHom D C hC BoolCat Obs := by
  simpa [colimitObservableTopCatHom, colimitEndomorphismTopCatHom] using
    (colimitObservable_invariant D C hC BoolCat Obs t)

end InfoGeometry.Topology.ColimitDynamics
