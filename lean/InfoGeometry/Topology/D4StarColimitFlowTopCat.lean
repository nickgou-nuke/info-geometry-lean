import InfoGeometry.Topology.D4StarColimitFlowHomeomorph
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology.ColimitDynamics

open CategoryTheory Limits

variable {J : Type*} [Category J]
variable (D : TopologicalDiscreteFlowSystem (J := J))
variable (C : Cocone D.carrier)
variable (hC : IsColimit C)

/-!
# `TopCat` time slices of the induced D₄-star colimit flow

This owner packages the already verified colimit homeomorphism as a `TopCat`
morphism and records its invertibility.
-/

noncomputable def colimitEndomorphismTopCatHom
    (t : ℤ) : C.pt ⟶ C.pt :=
  colimitEndomorphism D C hC t

@[simp] theorem colimitEndomorphismTopCatHom_apply
    (t : ℤ) (x : C.pt) :
    colimitEndomorphismTopCatHom D C hC t x =
      colimitEndomorphismHomeomorph D C hC t x :=
  rfl

theorem colimitEndomorphismTopCatHom_zero :
    colimitEndomorphismTopCatHom D C hC 0 = 𝟙 C.pt :=
  colimitEndomorphism_zero D C hC

theorem colimitEndomorphismTopCatHom_add
    (s t : ℤ) :
    colimitEndomorphismTopCatHom D C hC (s + t) =
      colimitEndomorphismTopCatHom D C hC t ≫
        colimitEndomorphismTopCatHom D C hC s :=
  colimitEndomorphism_add D C hC s t

theorem colimitEndomorphismTopCatHom_isIso
    (t : ℤ) :
    IsIso (colimitEndomorphismTopCatHom D C hC t) :=
  IsIso.mk ⟨colimitEndomorphism D C hC (-t),
    colimitEndomorphism_comp_neg D C hC t,
    colimitEndomorphism_neg_comp D C hC t⟩

end InfoGeometry.Topology.ColimitDynamics
