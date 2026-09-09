import InfoGeometry.Categorical.LogNilpotentModuleCategory

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
def unitObject : LogNilpotentModule 𝕜 where
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
    simp [unitObject, LogNilpotentModule.tensorObj, LogEndModule.tensorObj,
      LogEndModule.tensorObj_N_tmul]

/-- Inverse left unitor as a logarithmic intertwiner. -/
def leftUnitorInv (X : LogNilpotentModule 𝕜) :
    X ⟶ LogNilpotentModule.tensorObj unitObject X where
  hom := (TensorProduct.lid 𝕜 X).symm.toLinearMap
  comm := by
    ext x
    simp [unitObject, LogNilpotentModule.tensorObj, LogEndModule.tensorObj,
      LogEndModule.tensorObj_N_tmul]

/-- Left unitor isomorphism in the logarithmic category. -/
def leftUnitorIso (X : LogNilpotentModule 𝕜) :
    LogNilpotentModule.tensorObj unitObject X ≅ X where
  hom := leftUnitorHom X
  inv := leftUnitorInv X
  hom_inv_id := by
    apply LogEndModule.Hom.ext
    ext c x
    simp [leftUnitorHom, leftUnitorInv]
  inv_hom_id := by
    apply LogEndModule.Hom.ext
    ext x
    simp [leftUnitorHom, leftUnitorInv]

/-- Right unitor as a logarithmic intertwiner. -/
def rightUnitorHom (X : LogNilpotentModule 𝕜) :
    LogNilpotentModule.tensorObj X unitObject ⟶ X where
  hom := (TensorProduct.rid 𝕜 X).toLinearMap
  comm := by
    apply TensorProduct.ext'
    intro x c
    simp [unitObject, LogNilpotentModule.tensorObj, LogEndModule.tensorObj,
      LogEndModule.tensorObj_N_tmul]

/-- Inverse right unitor as a logarithmic intertwiner. -/
def rightUnitorInv (X : LogNilpotentModule 𝕜) :
    X ⟶ LogNilpotentModule.tensorObj X unitObject where
  hom := (TensorProduct.rid 𝕜 X).symm.toLinearMap
  comm := by
    ext x
    simp [unitObject, LogNilpotentModule.tensorObj, LogEndModule.tensorObj,
      LogEndModule.tensorObj_N_tmul]

/-- Right unitor isomorphism in the logarithmic category. -/
def rightUnitorIso (X : LogNilpotentModule 𝕜) :
    LogNilpotentModule.tensorObj X unitObject ≅ X where
  hom := rightUnitorHom X
  inv := rightUnitorInv X
  hom_inv_id := by
    apply LogEndModule.Hom.ext
    ext x c
    simp [rightUnitorHom, rightUnitorInv]
  inv_hom_id := by
    apply LogEndModule.Hom.ext
    ext x
    simp [rightUnitorHom, rightUnitorInv]

/-- Triangle coherence for the logarithmic associator and unitors.

Both paths from `(X ⊗ 𝟙) ⊗ Y` to `X ⊗ Y` agree. -/
theorem triangle_identity (X Y : LogNilpotentModule 𝕜) :
    (LogNilpotentModule.associatorIso X unitObject Y).hom ≫
        LogNilpotentModule.tensorHom (𝟙 X) (leftUnitorIso Y).hom =
      LogNilpotentModule.tensorHom (rightUnitorIso X).hom (𝟙 Y) := by
  apply LogEndModule.Hom.ext
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
