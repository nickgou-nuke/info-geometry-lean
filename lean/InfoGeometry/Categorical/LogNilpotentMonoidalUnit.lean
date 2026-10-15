import InfoGeometry.Categorical.LogNilpotentModuleCategory
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Categorical.LogNilpotentMonoidalUnit

Tensor unit and triangle coherence for finite-nilpotent logarithmic modules.

The tensor unit is the ground field with zero distinguished endomorphism.  The
canonical `TensorProduct.lid` and `TensorProduct.rid` equivalences intertwine
the primitive logarithmic endomorphisms and therefore lift to isomorphisms in
the logarithmic category.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogNilpotentMonoidalUnit

open CategoryTheory
open scoped TensorProduct

open InfoGeometry.Categorical.LogEndModuleCategory
open InfoGeometry.Categorical.LogEndModuleCategory.LogEndModule
open InfoGeometry.Categorical.LogNilpotentModuleCategory
open InfoGeometry.Categorical.LogNilpotentModuleCategory.LogNilpotentModule

universe u v

variable {𝕜 : Type u} [Field 𝕜]

/-- Tensor unit: the scalar field with zero logarithmic endomorphism. -/
def unitObject : LogNilpotentModule.{u, u} 𝕜 where
  toLogEndModule :=
    { V := 𝕜
      N := 0 }
  nilpotencyOrder := 1
  nilpotent := by simp

/-- Left unitor as a logarithmic intertwiner. -/
def leftUnitorHom (X : LogNilpotentModule 𝕜) :
    LogNilpotentModule.tensorObj unitObject X ⟶ X where
  hom := (TensorProduct.lid 𝕜 X).toLinearMap
  comm := by
    apply TensorProduct.ext'
    intro c x
    change 𝕜 at c
    change (TensorProduct.lid 𝕜 X.toLogEndModule.V)
        ((TensorProduct.map (0 : Module.End 𝕜 𝕜) (LinearMap.id : Module.End 𝕜 X) +
          TensorProduct.map (LinearMap.id : Module.End 𝕜 𝕜) X.toLogEndModule.N)
          (c ⊗ₜ[𝕜] x)) =
      X.toLogEndModule.N ((TensorProduct.lid 𝕜 X.toLogEndModule.V) (c ⊗ₜ[𝕜] x))
    rw [LinearMap.add_apply, TensorProduct.map_tmul, TensorProduct.map_tmul]
    simp [unitObject, TensorProduct.lid_tmul]

/-- Inverse left unitor as a logarithmic intertwiner. -/
def leftUnitorInv (X : LogNilpotentModule 𝕜) :
    X ⟶ LogNilpotentModule.tensorObj unitObject X where
  hom := (TensorProduct.lid 𝕜 X).symm.toLinearMap
  comm := by
    apply LinearMap.ext
    intro x
    change (TensorProduct.lid 𝕜 X.toLogEndModule.V).symm (X.toLogEndModule.N x) =
      (LogNilpotentModule.tensorObj unitObject X).N
        ((TensorProduct.lid 𝕜 X.toLogEndModule.V).symm x)
    rw [TensorProduct.lid_symm_apply]
    change (1 : 𝕜) ⊗ₜ[𝕜] X.toLogEndModule.N x =
      (TensorProduct.map (0 : Module.End 𝕜 𝕜) (LinearMap.id : Module.End 𝕜 X) +
        TensorProduct.map (LinearMap.id : Module.End 𝕜 𝕜) X.toLogEndModule.N)
        ((1 : 𝕜) ⊗ₜ[𝕜] x)
    rw [LinearMap.add_apply, TensorProduct.map_tmul, TensorProduct.map_tmul]
    simp

/-- Left unitor isomorphism in the logarithmic category. -/
def leftUnitorIso (X : LogNilpotentModule 𝕜) :
    LogNilpotentModule.tensorObj unitObject X ≅ X where
  hom := leftUnitorHom X
  inv := leftUnitorInv X
  hom_inv_id := by
    apply LogEndModule.Hom.ext
    apply LinearMap.ext
    intro z
    change (TensorProduct.lid 𝕜 X.toLogEndModule.V).symm
      ((TensorProduct.lid 𝕜 X.toLogEndModule.V) z) = z
    exact (TensorProduct.lid 𝕜 X.toLogEndModule.V).left_inv z
  inv_hom_id := by
    apply LogEndModule.Hom.ext
    apply LinearMap.ext
    intro z
    change (TensorProduct.lid 𝕜 X.toLogEndModule.V)
      ((TensorProduct.lid 𝕜 X.toLogEndModule.V).symm z) = z
    exact (TensorProduct.lid 𝕜 X.toLogEndModule.V).right_inv z

/-- Right unitor as a logarithmic intertwiner. -/
def rightUnitorHom (X : LogNilpotentModule 𝕜) :
    LogNilpotentModule.tensorObj X unitObject ⟶ X where
  hom := (TensorProduct.rid 𝕜 X).toLinearMap
  comm := by
    apply TensorProduct.ext'
    intro x c
    change 𝕜 at c
    change (TensorProduct.rid 𝕜 X.toLogEndModule.V)
        ((TensorProduct.map X.toLogEndModule.N (LinearMap.id : Module.End 𝕜 𝕜) +
          TensorProduct.map (LinearMap.id : Module.End 𝕜 X) (0 : Module.End 𝕜 𝕜))
          (x ⊗ₜ[𝕜] c)) =
      X.toLogEndModule.N ((TensorProduct.rid 𝕜 X.toLogEndModule.V) (x ⊗ₜ[𝕜] c))
    rw [LinearMap.add_apply, TensorProduct.map_tmul, TensorProduct.map_tmul]
    simp [unitObject, TensorProduct.rid_tmul]

/-- Inverse right unitor as a logarithmic intertwiner. -/
def rightUnitorInv (X : LogNilpotentModule 𝕜) :
    X ⟶ LogNilpotentModule.tensorObj X unitObject where
  hom := (TensorProduct.rid 𝕜 X).symm.toLinearMap
  comm := by
    apply LinearMap.ext
    intro x
    change (TensorProduct.rid 𝕜 X.toLogEndModule.V).symm (X.toLogEndModule.N x) =
      (LogNilpotentModule.tensorObj X unitObject).N
        ((TensorProduct.rid 𝕜 X.toLogEndModule.V).symm x)
    rw [TensorProduct.rid_symm_apply]
    change X.toLogEndModule.N x ⊗ₜ[𝕜] (1 : 𝕜) =
      (TensorProduct.map X.toLogEndModule.N (LinearMap.id : Module.End 𝕜 𝕜) +
        TensorProduct.map (LinearMap.id : Module.End 𝕜 X) (0 : Module.End 𝕜 𝕜))
        (x ⊗ₜ[𝕜] (1 : 𝕜))
    rw [LinearMap.add_apply, TensorProduct.map_tmul, TensorProduct.map_tmul]
    simp

/-- Right unitor isomorphism in the logarithmic category. -/
def rightUnitorIso (X : LogNilpotentModule 𝕜) :
    LogNilpotentModule.tensorObj X unitObject ≅ X where
  hom := rightUnitorHom X
  inv := rightUnitorInv X
  hom_inv_id := by
    apply LogEndModule.Hom.ext
    apply LinearMap.ext
    intro z
    change (TensorProduct.rid 𝕜 X.toLogEndModule.V).symm
      ((TensorProduct.rid 𝕜 X.toLogEndModule.V) z) = z
    exact (TensorProduct.rid 𝕜 X.toLogEndModule.V).left_inv z
  inv_hom_id := by
    apply LogEndModule.Hom.ext
    apply LinearMap.ext
    intro z
    change (TensorProduct.rid 𝕜 X.toLogEndModule.V)
      ((TensorProduct.rid 𝕜 X.toLogEndModule.V).symm z) = z
    exact (TensorProduct.rid 𝕜 X.toLogEndModule.V).right_inv z

/-- Triangle coherence for the logarithmic associator and unitors.

Both paths from `(X ⊗ 𝟙) ⊗ Y` to `X ⊗ Y` agree. -/
theorem triangle_identity (X Y : LogNilpotentModule 𝕜) :
    (LogNilpotentModule.associatorIso X unitObject Y).hom ≫
        LogNilpotentModule.tensorHom (𝟙 X) (leftUnitorIso Y).hom =
      LogNilpotentModule.tensorHom (rightUnitorIso X).hom (𝟙 Y) := by
  apply LogEndModule.Hom.ext
  dsimp [unitObject]
  apply TensorProduct.ext_threefold
  intro x c y
  change x ⊗ₜ[𝕜] (TensorProduct.lid 𝕜 Y.toLogEndModule.V (c ⊗ₜ[𝕜] y)) =
    (TensorProduct.rid 𝕜 X.toLogEndModule.V (x ⊗ₜ[𝕜] c)) ⊗ₜ[𝕜] y
  simp [LogNilpotentModule.associatorIso, LogEndModule.associatorHom,
    LogNilpotentModule.tensorHom, leftUnitorIso, leftUnitorHom,
    rightUnitorIso, rightUnitorHom, LogEndModule.tensorHom,
    TensorProduct.assoc_tmul, TensorProduct.lid_tmul, TensorProduct.rid_tmul,
    TensorProduct.map_tmul, TensorProduct.assoc]
  rfl

end InfoGeometry.Categorical.LogNilpotentMonoidalUnit
