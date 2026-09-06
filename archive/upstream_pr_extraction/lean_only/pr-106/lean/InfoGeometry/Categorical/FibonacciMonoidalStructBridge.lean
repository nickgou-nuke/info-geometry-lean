import InfoGeometry.Categorical.FibonacciBraidedCategory

/-!
# Native monoidal-structure interface for the skeletal Fibonacci carrier

The object tensor, whiskering maps, tensor-hom map, and equality-transport
coherences are already proved in `FibonacciBraidedCategory`.  This owner
packages exactly that data as Mathlib's `MonoidalCategoryStruct`.  It does not
claim the nontrivial Fibonacci `F`/`R` associator or a braided-category
instance.
-/

noncomputable section

namespace InfoGeometry.Categorical.FibonacciBraidedCategory

open CategoryTheory
open CategoryTheory.MonoidalCategory
open InfoGeometry.Categorical.FibonacciFusionCategoryData
open InfoGeometry.Categorical.FibonacciHomSpace
open scoped CategoryTheory.MonoidalCategory

noncomputable instance fibMonoidalCategoryStruct : MonoidalCategoryStruct FibCat where
  tensorObj := fibTensorObj
  whiskerLeft := fibWhiskerLeft
  whiskerRight := fibWhiskerRight
  tensorHom := fibTensorHom
  tensorUnit := fibTensorUnit
  associator := fibAssociator
  leftUnitor := fibLeftUnitor
  rightUnitor := fibRightUnitor

@[simp] theorem fibMonoidalCategoryStruct_tensorObj (X Y : FibCat) :
    (X ⊗ Y) = fibTensorObj X Y := rfl

@[simp] theorem fibMonoidalCategoryStruct_tensorUnit :
    (𝟙_ FibCat) = fibTensorUnit := rfl

/-- The installed monoidal structure satisfies the skeletal pentagon law. -/
theorem fibMonoidalCategoryStruct_pentagon (W X Y Z : FibCat) :
    MonoidalCategory.Pentagon W X Y Z := by
  change
    fibWhiskerRight (fibAssociator W X Y).hom Z ≫
        (fibAssociator W (fibTensorObj X Y) Z).hom ≫
        fibWhiskerLeft W (fibAssociator X Y Z).hom =
      (fibAssociator (fibTensorObj W X) Y Z).hom ≫
        (fibAssociator W X (fibTensorObj Y Z)).hom
  exact (fibAssociator_pentagon W X Y Z).symm

/-- The installed monoidal structure satisfies the skeletal triangle law. -/
theorem fibMonoidalCategoryStruct_triangle (X Y : FibCat) :
    (fibAssociator X fibTensorUnit Y).hom ≫
        fibWhiskerLeft X (fibLeftUnitor Y).hom =
      fibWhiskerRight (fibRightUnitor X).hom Y := by
  exact fibAssociator_triangle X Y

theorem fibMonoidalCategoryStruct_associator_naturality_id
    (X Y Z : FibCat) :
    FibHom.comp
        (fibTensorHom (fibTensorHom (FibHom.id X) (FibHom.id Y))
          (FibHom.id Z))
        (fibAssociator X Y Z).hom =
      FibHom.comp
        (fibAssociator X Y Z).hom
        (fibTensorHom (FibHom.id X)
          (fibTensorHom (FibHom.id Y) (FibHom.id Z))) := by
  ext <;>
      simp [fibTensorHom, FibHom.comp, FibHom.id, Matrix.reindex,
      blockDiag2, blockDiag3, kron]

theorem fibMonoidalCategoryStruct_leftUnitor_naturality_id
    (X : FibCat) :
    FibHom.comp
        (fibWhiskerLeft fibTensorUnit (FibHom.id X))
        (fibLeftUnitor X).hom =
      FibHom.comp (fibLeftUnitor X).hom (FibHom.id X) := by
  ext <;>
    simp [fibWhiskerLeft, fibTensorHom, FibHom.comp, FibHom.id,
      Matrix.reindex, blockDiag2, blockDiag3, kron]

theorem fibMonoidalCategoryStruct_rightUnitor_naturality_id
    (X : FibCat) :
    FibHom.comp
        (fibWhiskerRight (FibHom.id X) fibTensorUnit)
        (fibRightUnitor X).hom =
      FibHom.comp (fibRightUnitor X).hom (FibHom.id X) := by
  ext <;>
      simp [fibWhiskerRight, fibTensorHom, FibHom.comp, FibHom.id,
      Matrix.reindex, blockDiag2, blockDiag3, kron]

end InfoGeometry.Categorical.FibonacciBraidedCategory
