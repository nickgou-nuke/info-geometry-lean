import InfoGeometry.Topology.D4StarColimitFlowInverse
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology.ColimitDynamics

open CategoryTheory Limits

variable {J : Type*} [Category J]
variable (D : TopologicalDiscreteFlowSystem (J := J))
variable (C : Cocone D.carrier)
variable (hC : IsColimit C)

/-!
# Homeomorphisms of the induced D₄-star colimit flow

The colimit endomorphism already carries a two-sided inverse at time `-t`.
This file packages that inverse data as a `Homeomorph`, without changing the
underlying topological content.
-/

noncomputable def colimitEndomorphismHomeomorph
    (t : ℤ) : C.pt ≃ₜ C.pt where
  toFun := fun x => colimitEndomorphism D C hC t x
  invFun := fun x => colimitEndomorphism D C hC (-t) x
  left_inv := by
    intro x
    have h := colimitEndomorphism_comp_neg D C hC t
    simpa [Category.comp_apply] using congrArg (fun f : C.pt ⟶ C.pt => f x) h
  right_inv := by
    intro x
    have h := colimitEndomorphism_neg_comp D C hC t
    simpa [Category.comp_apply] using congrArg (fun f : C.pt ⟶ C.pt => f x) h
  continuous_toFun := (colimitEndomorphism D C hC t).hom.continuous
  continuous_invFun := (colimitEndomorphism D C hC (-t)).hom.continuous

@[simp] theorem colimitEndomorphismHomeomorph_apply
    (t : ℤ) (x : C.pt) :
    colimitEndomorphismHomeomorph D C hC t x =
      colimitEndomorphism D C hC t x :=
  rfl

theorem colimitEndomorphismHomeomorph_zero_apply
    (x : C.pt) :
    colimitEndomorphismHomeomorph D C hC 0 x = x := by
  simpa [Category.comp_apply] using congrArg (fun f : C.pt ⟶ C.pt => f x)
    (colimitEndomorphism_zero (D := D) (C := C) (hC := hC))

theorem colimitEndomorphismHomeomorph_add_apply
    (s t : ℤ) (x : C.pt) :
    colimitEndomorphismHomeomorph D C hC (s + t) x =
      colimitEndomorphismHomeomorph D C hC s
        (colimitEndomorphismHomeomorph D C hC t x) := by
  simpa [colimitEndomorphismHomeomorph, Category.comp_apply] using congrArg (fun f : C.pt ⟶ C.pt => f x)
    (colimitEndomorphism_add (D := D) (C := C) (hC := hC) s t)

end InfoGeometry.Topology.ColimitDynamics
