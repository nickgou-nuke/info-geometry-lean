import Mathlib.Tactic
import InfoGeometry.Algebra.AnyonFiniteSpinBraid

open InfoGeometry.Algebra.AnyonFiniteSpinBraid

namespace InfoGeometry.Categorical.GrothendieckTeichmullerBraidBridge

/-- Every monoid homomorphism carries a pair satisfying the `B₃` braid
relation to another such pair. -/
theorem gt_automorphism_preserves_b3
    {G H : Type*} [Monoid G] [Monoid H]
    (ϕ : G →* H) (σ₁ σ₂ : G)
    (hbraid : σ₁ * σ₂ * σ₁ = σ₂ * σ₁ * σ₂) :
    ϕ σ₁ * ϕ σ₂ * ϕ σ₁ = ϕ σ₂ * ϕ σ₁ * ϕ σ₂ := by
  simpa only [map_mul] using congrArg ϕ hbraid

theorem gt_braid_action_exists
    {G H : Type*} [Monoid G] [Monoid H]
    (ϕ : G →* H) (σ₁ σ₂ : G)
    (hbraid : σ₁ * σ₂ * σ₁ = σ₂ * σ₁ * σ₂) :
    ∃ τ₁ τ₂ : H, τ₁ * τ₂ * τ₁ = τ₂ * τ₁ * τ₂ :=
  ⟨ϕ σ₁, ϕ σ₂, gt_automorphism_preserves_b3 ϕ σ₁ σ₂ hbraid⟩

end InfoGeometry.Categorical.GrothendieckTeichmullerBraidBridge
