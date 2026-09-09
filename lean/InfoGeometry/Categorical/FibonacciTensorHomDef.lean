import Mathlib.CategoryTheory.EqToHom
import InfoGeometry.Categorical.FibonacciBraidedCategory

/-!
# Tensor-hom factorisation for the skeletal Fibonacci carrier

This is the first bundled-monoidal law separated from the large block-matrix
owner.  It identifies the tensor morphism with right whiskering followed by
left whiskering, using the already proved composition law for `fibTensorHom`.
-/

noncomputable section

namespace InfoGeometry.Categorical.FibonacciBraidedCategory

open CategoryTheory
open InfoGeometry.Categorical.FibonacciFusionCategoryData
open InfoGeometry.Categorical.FibonacciHomSpace

theorem fibEqToHom_comp_eqToHom
    {X Y Z : FibCat} (p : X = Y) (q : Y = Z) :
    FibHom.comp (CategoryTheory.eqToHom p) (CategoryTheory.eqToHom q) =
      CategoryTheory.eqToHom (p.trans q) := by
  cases p
  cases q
  change FibHom.comp (FibHom.id X) (FibHom.id X) = FibHom.id X
  ext <;> simp [FibHom.comp, FibHom.id, Matrix.mul_apply]

theorem fibTensorHom_eqToHom_eqToHom
    {X₁ X₂ Y₁ Y₂ : FibCat} (p : X₁ = X₂) (q : Y₁ = Y₂) :
    fibTensorHom (CategoryTheory.eqToHom p) (CategoryTheory.eqToHom q) =
      CategoryTheory.eqToHom (congrArg₂ fibTensorObj p q) := by
  cases p
  cases q
  exact fibTensorHom_id X₁ Y₁

theorem fibTensorHom_eq_whisker_comp
    {X₁ X₂ Y₁ Y₂ : FibCat} (f : FibHom X₁ X₂) (g : FibHom Y₁ Y₂) :
    fibTensorHom f g =
      FibHom.comp (fibWhiskerRight f Y₁)
        (fibWhiskerLeft X₂ g) := by
  unfold fibWhiskerRight fibWhiskerLeft
  calc
    fibTensorHom f g =
        fibTensorHom
          (FibHom.comp f (FibHom.id X₂))
          (FibHom.comp (FibHom.id Y₁) g) := by
      congr 1 <;> ext <;> simp [FibHom.comp, FibHom.id]
    _ = FibHom.comp
          (fibTensorHom f (FibHom.id Y₁))
          (fibTensorHom (FibHom.id X₂) g) :=
      fibTensorHom_comp f (FibHom.id X₂) (FibHom.id Y₁) g

end InfoGeometry.Categorical.FibonacciBraidedCategory
