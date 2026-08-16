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

end InfoGeometry.Categorical.FibonacciBraidedCategory
