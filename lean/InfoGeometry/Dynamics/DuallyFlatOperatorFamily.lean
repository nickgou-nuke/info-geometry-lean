import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# A minimal dually-flat operator-family contract

This owner records only the algebraic inverse maps and the Legendre identity.
It does not assert differentiability, convexity, gradients, or a physical
interpretation.
-/

namespace InfoGeometry.Dynamics.DuallyFlat

variable {S M : Type*} [AddCommGroup S] [AddCommGroup M]
variable [Module ℝ S] [Module ℝ M]
variable (interaction : S →ₗ[ℝ] M →ₗ[ℝ] ℝ)

structure OperatorFamily (interaction : S →ₗ[ℝ] M →ₗ[ℝ] ℝ) where
  Psi : S → ℝ
  entropy : M → ℝ
  spaceToMatter : S → M
  matterToSpace : M → S
  left_inv : ∀ x, matterToSpace (spaceToMatter x) = x
  right_inv : ∀ y, spaceToMatter (matterToSpace y) = y
  legendre_identity : ∀ x,
    Psi x + entropy (spaceToMatter x) = interaction x (spaceToMatter x)

namespace OperatorFamily

variable (F : OperatorFamily interaction)

noncomputable def bregmanDivergence (x₁ x₂ : S) : ℝ :=
  F.Psi x₁ + F.entropy (F.spaceToMatter x₂) -
    interaction x₁ (F.spaceToMatter x₂)

theorem bregmanDivergence_self (x : S) :
    bregmanDivergence interaction F x x = 0 := by
  dsimp [bregmanDivergence]
  rw [F.legendre_identity]
  ring

theorem bregmanDivergence_dual_reorder (x₁ x₂ : S) :
    bregmanDivergence interaction F x₁ x₂ =
      F.entropy (F.spaceToMatter x₂) + F.Psi x₁ -
        interaction x₁ (F.spaceToMatter x₂) := by
  unfold bregmanDivergence
  ring

theorem spaceToMatter_injective : Function.Injective F.spaceToMatter := by
  intro x y h
  rw [← F.left_inv x, ← F.left_inv y, h]

theorem spaceToMatter_surjective : Function.Surjective F.spaceToMatter := by
  intro y
  exact ⟨F.matterToSpace y, F.right_inv y⟩

theorem spaceToMatter_bijective : Function.Bijective F.spaceToMatter :=
  ⟨spaceToMatter_injective interaction F, spaceToMatter_surjective interaction F⟩

end OperatorFamily
end InfoGeometry.Dynamics.DuallyFlat
