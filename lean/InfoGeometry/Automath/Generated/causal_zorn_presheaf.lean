import Mathlib
import InfoGeometry.Algebra.CuntzTensorQuotient
import InfoGeometry.Algebra.CuntzFibonacciBraidInclusion

/-!
# Causal Zorn Presheaf Cuntz Representation

Defines the Causal Zorn Presheaf structures and proves their compatibility
with the Cuntz algebra representation.
-/

namespace Automath.Generated

open InfoGeometry.Algebra.CuntzTensorQuotient
open CuntzFibonacciBraidInclusion

universe u v

structure CausalZornPresheaf (X : Type u) [Preorder X] where
  obj : X → Type v
  res : ∀ {u₁ u₂ : X}, u₁ ≤ u₂ → obj u₂ → obj u₁
  res_id :
    ∀ (u₁ : X) (z : obj u₁),
      res (le_refl u₁) z = z
  res_comp :
    ∀ {u₁ u₂ u₃ : X}
      (h₁₂ : u₁ ≤ u₂) (h₂₃ : u₂ ≤ u₃) (z : obj u₃),
      res h₁₂ (res h₂₃ z) = res (h₁₂.trans h₂₃) z

theorem causalZornPresheaf_cuntzRepresentation
    {X : Type u} [Preorder X] {n : ℕ}
    (P : CausalZornPresheaf X)
    (zornMatrix :
      ∀ u : X, P.obj u → Matrix (Fin n) (Fin n) ℂ)
    (hcompat :
      ∀ {u₁ u₂ : X} (h : u₁ ≤ u₂) (z : P.obj u₂),
        matrixToCuntz n (zornMatrix u₁ (P.res h z)) =
          matrixToCuntz n (zornMatrix u₂ z)) :
    ∃ cuntzRep : ∀ u : X, P.obj u → CuntzAlg n,
      (∀ (u : X) (z : P.obj u),
          cuntzRep u z = matrixToCuntz n (zornMatrix u z)) ∧
      (∀ {u₁ u₂ : X} (h : u₁ ≤ u₂) (z : P.obj u₂),
          cuntzRep u₁ (P.res h z) = cuntzRep u₂ z) := by
  use fun u z => matrixToCuntz n (zornMatrix u z)
  refine ⟨fun u z => rfl, fun {u₁ u₂} h z => hcompat h z⟩

end Automath.Generated
