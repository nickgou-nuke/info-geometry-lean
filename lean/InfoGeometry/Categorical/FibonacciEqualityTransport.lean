import InfoGeometry.Categorical.FibonacciTensorHomDef
import InfoGeometry.Categorical.FibonacciBraidedCategory

noncomputable section

namespace InfoGeometry.Categorical.FibonacciBraidedCategory

open CategoryTheory
open InfoGeometry.Categorical.FibonacciHomSpace

/-- Tensoring two equality transports and then applying a third equality
transport is the equality transport along the composite object equality.

This is the small path-calculus lemma used to keep the skeletal coherence
proofs independent of the concrete matrix reindexing implementation. -/
theorem fibTensorHom_eqToHom_comp_eqToHom
    {X₁ X₂ Y₁ Y₂ Z : FibCat}
    (hX : X₁ = X₂) (hY : Y₁ = Y₂)
    (hZ : fibTensorObj X₂ Y₂ = Z) :
    FibHom.comp
        (fibTensorHom (CategoryTheory.eqToHom hX)
          (CategoryTheory.eqToHom hY))
        (CategoryTheory.eqToHom hZ) =
      CategoryTheory.eqToHom
        ((congrArg₂ fibTensorObj hX hY).trans hZ) := by
  rw [fibTensorHom_eqToHom_eqToHom hX hY]
  exact fibEqToHom_comp_eqToHom (congrArg₂ fibTensorObj hX hY) hZ

/-- The corresponding three-factor equality transport, before any reassociation
of the underlying fusion object is used. -/
theorem fibTensorHom_three_eqToHom_comp_eqToHom
    {X₁ X₂ Y₁ Y₂ Z₁ Z₂ W : FibCat}
    (hX : X₁ = X₂) (hY : Y₁ = Y₂) (hZ : Z₁ = Z₂)
    (hW : fibTensorObj (fibTensorObj X₂ Y₂) Z₂ = W) :
    FibHom.comp
        (fibTensorHom
          (fibTensorHom (CategoryTheory.eqToHom hX)
            (CategoryTheory.eqToHom hY))
          (CategoryTheory.eqToHom hZ))
        (CategoryTheory.eqToHom hW) =
      CategoryTheory.eqToHom
        ((congrArg₂ fibTensorObj
          (congrArg₂ fibTensorObj hX hY) hZ).trans hW) := by
  rw [fibTensorHom_eqToHom_eqToHom hX hY]
  rw [fibTensorHom_eqToHom_eqToHom
    (congrArg₂ fibTensorObj hX hY) hZ]
  exact fibEqToHom_comp_eqToHom
    (congrArg₂ fibTensorObj (congrArg₂ fibTensorObj hX hY) hZ) hW

/-- Naturality of the skeletal associator for equality-transport morphisms.
This is the equality-transport fragment of associator naturality; arbitrary
matrix morphisms require an additional reindexing theorem. -/
theorem fibAssociator_naturality_eqToHom
    {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : FibCat}
    (hX : X₁ = X₂) (hY : Y₁ = Y₂) (hZ : Z₁ = Z₂) :
    FibHom.comp
        (fibTensorHom
          (fibTensorHom (CategoryTheory.eqToHom hX)
            (CategoryTheory.eqToHom hY))
          (CategoryTheory.eqToHom hZ))
        (fibAssociator X₂ Y₂ Z₂).hom =
      FibHom.comp
        (fibAssociator X₁ Y₁ Z₁).hom
        (fibTensorHom (CategoryTheory.eqToHom hX)
          (fibTensorHom (CategoryTheory.eqToHom hY)
            (CategoryTheory.eqToHom hZ))) := by
  rw [fibAssociator_hom, fibAssociator_hom]
  rw [fibTensorHom_three_eqToHom_comp_eqToHom hX hY hZ
    (fibTensorObj_assoc X₂ Y₂ Z₂)]
  rw [fibTensorHom_eqToHom_eqToHom hY hZ]
  rw [fibTensorHom_eqToHom_eqToHom hX
    (congrArg₂ fibTensorObj hY hZ)]
  rw [fibEqToHom_comp_eqToHom]

end InfoGeometry.Categorical.FibonacciBraidedCategory
