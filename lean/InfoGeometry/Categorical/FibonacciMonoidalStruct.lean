import InfoGeometry.Categorical.FibonacciMonoidalStructBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Compatibility names for the canonical Fibonacci monoidal struct owner

The installed `MonoidalCategoryStruct` is owned by
`FibonacciMonoidalStructBridge`.  This file only forwards a small API under
the newer namespace; it does not introduce a second tensor carrier or a
second typeclass instance.
-/

namespace InfoGeometry.Categorical.FibonacciMonoidalStruct

open CategoryTheory
open InfoGeometry.Categorical.FibonacciHomSpace
open InfoGeometry.Categorical.FibonacciFusionCategoryData
open InfoGeometry.Categorical.FibonacciBraidedCategory

noncomputable def fibMonoidalStruct : MonoidalCategoryStruct FibCat :=
  inferInstance

theorem fibMonoidalStruct_tensorObj (X Y : FibCat) :
    fibMonoidalStruct.tensorObj X Y = fibTensorObj X Y :=
  rfl

theorem fibMonoidalStruct_tensorUnit :
    fibMonoidalStruct.tensorUnit = fibTensorUnit :=
  rfl

theorem fibMonoidalStruct_tensorHom_def
    {X₁ Y₁ X₂ Y₂ : FibCat}
    (f : FibHom X₁ Y₁) (g : FibHom X₂ Y₂) :
    fibMonoidalStruct.tensorHom f g =
      FibHom.comp
        (fibMonoidalStruct.whiskerRight f X₂)
        (fibMonoidalStruct.whiskerLeft Y₁ g) := by
  change fibTensorHom f g =
    FibHom.comp
      (fibTensorHom f (FibHom.id X₂))
      (fibTensorHom (FibHom.id Y₁) g)
  calc
    fibTensorHom f g =
        fibTensorHom
          (FibHom.comp f (FibHom.id Y₁))
          (FibHom.comp (FibHom.id X₂) g) := by
      congr 1 <;> ext <;> simp [FibHom.comp, FibHom.id]
    _ = FibHom.comp
        (fibTensorHom f (FibHom.id X₂))
        (fibTensorHom (FibHom.id Y₁) g) := by
      exact fibTensorHom_comp f (FibHom.id Y₁)
        (FibHom.id X₂) g

theorem fibMonoidalStruct_whiskerLeft_id (X Y : FibCat) :
    fibMonoidalStruct.whiskerLeft X (FibHom.id Y) =
      FibHom.id (fibTensorObj X Y) := by
  change fibTensorHom (FibHom.id X) (FibHom.id Y) = _
  exact fibTensorHom_id X Y

theorem fibMonoidalStruct_id_whiskerRight (X Y : FibCat) :
    fibMonoidalStruct.whiskerRight (FibHom.id X) Y =
      FibHom.id (fibTensorObj X Y) := by
  change fibTensorHom (FibHom.id X) (FibHom.id Y) = _
  exact fibTensorHom_id X Y

theorem fibMonoidalStruct_tensorHom_comp
    {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : FibCat}
    (f₁ : FibHom X₁ Y₁) (f₂ : FibHom X₂ Y₂)
    (g₁ : FibHom Y₁ Z₁) (g₂ : FibHom Y₂ Z₂) :
    FibHom.comp
        (fibMonoidalStruct.tensorHom f₁ f₂)
        (fibMonoidalStruct.tensorHom g₁ g₂) =
      fibMonoidalStruct.tensorHom
        (FibHom.comp f₁ g₁) (FibHom.comp f₂ g₂) := by
  change FibHom.comp
      (fibTensorHom f₁ f₂) (fibTensorHom g₁ g₂) =
    fibTensorHom (FibHom.comp f₁ g₁) (FibHom.comp f₂ g₂)
  exact (fibTensorHom_comp f₁ g₁ f₂ g₂).symm

end InfoGeometry.Categorical.FibonacciMonoidalStruct
