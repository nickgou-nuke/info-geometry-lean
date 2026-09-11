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
    (t : ℤ) : TopCat.of C.pt ⟶ TopCat.of C.pt :=
  TopCat.ofHom
    { toFun := colimitEndomorphismHomeomorph D C hC t
      continuous_toFun :=
        (colimitEndomorphismHomeomorph D C hC t).continuous_toFun }

@[simp] theorem colimitEndomorphismTopCatHom_apply
    (t : ℤ) (x : C.pt) :
    colimitEndomorphismTopCatHom D C hC t x =
      colimitEndomorphismHomeomorph D C hC t x :=
  rfl

theorem colimitEndomorphismTopCatHom_zero :
    colimitEndomorphismTopCatHom D C hC 0 = 𝟙 (TopCat.of C.pt) := by
  ext x
  simp [colimitEndomorphismTopCatHom]

theorem colimitEndomorphismTopCatHom_add
    (s t : ℤ) :
    colimitEndomorphismTopCatHom D C hC (s + t) =
      colimitEndomorphismTopCatHom D C hC t ≫
        colimitEndomorphismTopCatHom D C hC s := by
  ext x
  simpa [TopCat.comp_app, colimitEndomorphismTopCatHom,
    colimitEndomorphismHomeomorph_add_apply] using
    (colimitEndomorphismHomeomorph_add_apply (D := D) (C := C) (hC := hC) s t x)

theorem colimitEndomorphismTopCatHom_isIso
    (t : ℤ) :
    IsIso (colimitEndomorphismTopCatHom D C hC t) := by
  refine IsIso.mk ⟨TopCat.ofHom
    { toFun := (colimitEndomorphismHomeomorph D C hC t).symm
      continuous_toFun :=
        (colimitEndomorphismHomeomorph D C hC t).symm.continuous_toFun }, ?_, ?_⟩
  · ext x
    simpa [colimitEndomorphismTopCatHom, TopCat.comp_app, TopCat.id_app, TopCat.ofHom]
      using (colimitEndomorphismHomeomorph D C hC t).symm_apply_apply x
  · ext x
    simpa [colimitEndomorphismTopCatHom, TopCat.comp_app, TopCat.id_app, TopCat.ofHom]
      using (colimitEndomorphismHomeomorph D C hC t).apply_symm_apply x

end InfoGeometry.Topology.ColimitDynamics
