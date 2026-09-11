import InfoGeometry.Categorical.LogNilpotentModuleCategory
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.HadjiivanovLogConnectionBraidBridge

/-!
# InfoGeometry.Categorical.HadjiivanovLogNilpotentBraidAdapter

Nearest categorical adapter from the existing Hadjiivanov braid-frame owner to
the tensor-closed logarithmic nilpotent category.

The existing braid frame supplies:

* a `B₃` representation by complex-linear equivalences;
* three square-zero nilpotent residue directions;
* an exact intertwining law transporting each residue direction by the braid
  permutation.

This file packages each color residue as a `LogNilpotentModule ℂ` of certified
order two and packages every braid transport as a morphism between the
corresponding color objects.

No claim is made here that this one-fiber `B₃` action is already the two-object
categorical braiding `c_{X,Y} : X ⊗ Y ≅ Y ⊗ X`.
-/

noncomputable section

namespace InfoGeometry.Categorical.HadjiivanovLogNilpotentBraidAdapter

open CategoryTheory
open InfoGeometry.Categorical.LogEndModuleCategory
open InfoGeometry.Categorical.LogNilpotentModuleCategory
open InfoGeometry.Categorical.LogNilpotentModuleCategory.LogNilpotentModule
open InfoGeometry.Projective.HadjiivanovLogConnectionBraidBridge
open InfoGeometry.Projective.ProjectiveNullBoundaryBraidEquivariance

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A color-selected Hadjiivanov nilpotent residue as a certified rank-two
logarithmic nilpotent object. -/
def colorObject (F : LogResidueBraidFrame V) (a : Fin 3) :
    LogNilpotentModule ℂ where
  toLogEndModule :=
    { V := V
      N := F.nilpotent a }
  nilpotencyOrder := 2
  nilpotent := by
    simpa [pow_two, Module.End.mul_eq_comp] using F.nilpotent_sq a

/-- A braid element becomes a logarithmic intertwiner from the color `a`
residue object to its braid-permuted residue object. -/
def braidHom (F : LogResidueBraidFrame V)
    (g : BraidGroup) (a : Fin 3) :
    colorObject F a ⟶ colorObject F (braidPermutation g a) where
  hom := (F.representation g).toLinearMap
  comm := by
    ext v
    exact F.nilpotent_intertwines g a v

@[simp]
theorem braidHom_apply
    (F : LogResidueBraidFrame V) (g : BraidGroup) (a : Fin 3) (v : V) :
    (braidHom F g a).hom v = F.representation g v :=
  rfl

/-- The identity braid acts by the identity logarithmic morphism. -/
theorem braidHom_one_apply
    (F : LogResidueBraidFrame V) (a : Fin 3) (v : V) :
    (braidHom F 1 a).hom v = v := by
  change (F.representation 1).toLinearMap v = v
  rw [map_one]
  exact LinearMap.id_apply v

/-- Multiplication in `B₃` is represented by composition on the underlying
logarithmic carriers. -/
theorem braidHom_mul_apply
    (F : LogResidueBraidFrame V) (g k : BraidGroup) (a : Fin 3) (v : V) :
    (braidHom F (g * k) a).hom v =
      F.representation g (F.representation k v) := by
  change (F.representation (g * k)).toLinearMap v =
    F.representation g (F.representation k v)
  rw [map_mul]
  rfl

/-- The categorical morphism equation is exactly the pre-existing nilpotent
intertwining law. -/
theorem braidHom_intertwines
    (F : LogResidueBraidFrame V) (g : BraidGroup) (a : Fin 3) :
    (braidHom F g a).hom.comp (colorObject F a).N =
      (colorObject F (braidPermutation g a)).N.comp
        (braidHom F g a).hom :=
  (braidHom F g a).comm

/-- The source and target objects both retain certified square-zero residue
operators, while their tensor product is automatically certified cube-zero by
the general `m+n-1` closure theorem. -/
theorem tensor_color_objects_cube_zero
    (F : LogResidueBraidFrame V) (a b : Fin 3) :
    (LogNilpotentModule.tensorObj (colorObject F a) (colorObject F b)).N ^ 3 = 0 := by
  exact InfoGeometry.Categorical.LogEndModuleNilpotentClosure.tensorObj_cube_zero_of_sq_zero
    (colorObject F a).toLogEndModule
    (colorObject F b).toLogEndModule
    (by simpa [pow_two, Module.End.mul_eq_comp] using F.nilpotent_sq a)
    (by simpa [pow_two, Module.End.mul_eq_comp] using F.nilpotent_sq b)

end InfoGeometry.Categorical.HadjiivanovLogNilpotentBraidAdapter
