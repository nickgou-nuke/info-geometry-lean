import Mathlib.Algebra.Module.LinearMap.End
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Equivariant branching maps

A Hopf coproduct distributes a symmetry action over an output tensor product.
The actual branching of states is a separate linear map

`B : Vᵢₙ →ₗ[R] V₁ ⊗[R] V₂`.

This file states equivariance directly as an equality of Mathlib linear maps.
No morphism record or proof-carrying witness is introduced.
-/

namespace InfoGeometry.Algebra.EquivariantBranching

variable {R H V₀ V₁ V₂ V₃ : Type*}
variable [CommSemiring R]
variable [AddCommMonoid V₀] [Module R V₀]
variable [AddCommMonoid V₁] [Module R V₁]
variable [AddCommMonoid V₂] [Module R V₂]
variable [AddCommMonoid V₃] [Module R V₃]

/-- The identity map intertwines every linear action with itself. -/
theorem id_intertwines (ρ : H → Module.End R V₀) (h : H) :
    (LinearMap.id : V₀ →ₗ[R] V₀).comp (ρ h) =
      (ρ h).comp LinearMap.id := by
  ext v
  rfl

/-- Intertwining linear maps are closed under composition. -/
theorem comp_intertwines
    (ρ₀ : H → Module.End R V₀)
    (ρ₁ : H → Module.End R V₁)
    (ρ₂ : H → Module.End R V₂)
    (B : V₀ →ₗ[R] V₁)
    (C : V₁ →ₗ[R] V₂)
    (hB : ∀ h, B.comp (ρ₀ h) = (ρ₁ h).comp B)
    (hC : ∀ h, C.comp (ρ₁ h) = (ρ₂ h).comp C)
    (h : H) :
    (C.comp B).comp (ρ₀ h) = (ρ₂ h).comp (C.comp B) := by
  calc
    (C.comp B).comp (ρ₀ h) = C.comp (B.comp (ρ₀ h)) := by
      simp only [LinearMap.comp_assoc]
    _ = C.comp ((ρ₁ h).comp B) := by rw [hB h]
    _ = (C.comp (ρ₁ h)).comp B := by
      simp only [LinearMap.comp_assoc]
    _ = ((ρ₂ h).comp C).comp B := by rw [hC h]
    _ = (ρ₂ h).comp (C.comp B) := by
      simp only [LinearMap.comp_assoc]

/-- An equivariant map sends vectors annihilated by an input action to vectors
annihilated by the corresponding output action. -/
theorem maps_annihilated_state
    (ρ₀ : H → Module.End R V₀)
    (ρ₁ : H → Module.End R V₁)
    (B : V₀ →ₗ[R] V₁)
    (hB : ∀ h, B.comp (ρ₀ h) = (ρ₁ h).comp B)
    (h : H) (v : V₀)
    (hv : ρ₀ h v = 0) :
    ρ₁ h (B v) = 0 := by
  have hintertwine := LinearMap.congr_fun (hB h) v
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hv, map_zero] at hintertwine
  exact hintertwine.symm

section TensorBranch

variable [AddCommMonoid V₃] [Module R V₃]

/--
A state branching map into a tensor product transports annihilated input
states whenever it intertwines the input action with the already-defined
tensor-product action.

The output action is an explicit argument: constructing it from a Hopf
coproduct is a separate theorem.
-/
theorem tensor_branch_maps_annihilated_state
    (ρin : H → Module.End R V₀)
    (ρout : H → Module.End R (TensorProduct R V₁ V₂))
    (B : V₀ →ₗ[R] TensorProduct R V₁ V₂)
    (hB : ∀ h, B.comp (ρin h) = (ρout h).comp B)
    (h : H) (v : V₀)
    (hv : ρin h v = 0) :
    ρout h (B v) = 0 :=
  maps_annihilated_state ρin ρout B hB h v hv

end TensorBranch

end InfoGeometry.Algebra.EquivariantBranching
