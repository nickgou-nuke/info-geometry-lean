import InfoGeometry.Categorical.FibonacciMonoidalStructBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Tensor-hom factorization for the Fibonacci Hom-space carrier

This is the general tensor-hom identity needed by Mathlib's monoidal
interface.  It uses the existing block-matrix tensor product and its
composition theorem; it does not promote the representation-level `F` block.
-/

namespace InfoGeometry.Categorical.FibonacciBraidedCategory

open CategoryTheory
open InfoGeometry.Categorical.FibonacciHomSpace

theorem fibTensorHom_def
    {X₁ Y₁ X₂ Y₂ : FibCat}
    (f : FibHom X₁ X₂) (g : FibHom Y₁ Y₂) :
    fibTensorHom f g =
      FibHom.comp
        (fibWhiskerRight f Y₁)
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
