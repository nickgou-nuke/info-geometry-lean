/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

/-!
# Natural transport of derivation-based connections under homomorphisms

The coefficient map and direction map need not be surjective or injective.
The target connection and both actions are required to intertwine on source
directions and coefficients. The conclusions apply to those images only.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

open InfoGeometry.Algebra

variable {R A B : Type*} [CommRing R]
variable [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable {K : DerivationLieLane R A} {K' : DerivationLieLane R B}

/-- The CE zero differential is natural on the images of two compatible
homomorphisms. -/
theorem exteriorDerivativeZero_hom_apply
    (σ : K.L →ₗ⁅R⁆ K'.L) (f : A →ₐ[R] B)
    (hact : ∀ x a, K'.operatorAction (σ x) (f a) = f (K.operatorAction x a))
    (x : K.L) (a : A) :
    exteriorDerivativeZero K' (f a) (σ x) = f (exteriorDerivativeZero K a x) := by
  exact hact x a

/-- The one-cochain differential intertwines provided the connection values
and derivation actions intertwine. -/
theorem exteriorDerivativeOne_hom_apply
    (σ : K.L →ₗ⁅R⁆ K'.L) (f : A →ₐ[R] B)
    (Γ : OneForm K) (Γ' : OneForm K')
    (hact : ∀ x a, K'.operatorAction (σ x) (f a) = f (K.operatorAction x a))
    (hΓ : ∀ x, Γ' (σ x) = f (Γ x)) (x y : K.L) :
    exteriorDerivativeOne K' Γ' (σ x) (σ y) = f (exteriorDerivativeOne K Γ x y) := by
  rw [exteriorDerivativeOne_apply, exteriorDerivativeOne_apply, ← σ.map_lie,
    hΓ, hΓ, hΓ, hact, hact, map_sub, map_sub]

/-- The noncommutative curvature transports along compatible homomorphisms,
including the bracket and the ordered connection products. -/
theorem connectionCurvature_hom_apply
    (σ : K.L →ₗ⁅R⁆ K'.L) (f : A →ₐ[R] B)
    (Γ : OneForm K) (Γ' : OneForm K')
    (hact : ∀ x a, K'.operatorAction (σ x) (f a) = f (K.operatorAction x a))
    (hΓ : ∀ x, Γ' (σ x) = f (Γ x)) (x y : K.L) :
    connectionCurvature K' Γ' (σ x) (σ y) = f (connectionCurvature K Γ x y) := by
  rw [connectionCurvature_apply, connectionCurvature_apply, ← σ.map_lie]
  simp only [hΓ, hact, map_sub, map_add, map_mul]

/-- The adjoint covariant action transports on source coefficients. -/
theorem covariantDerivative_hom_apply
    (σ : K.L →ₗ⁅R⁆ K'.L) (f : A →ₐ[R] B)
    (Γ : OneForm K) (Γ' : OneForm K')
    (hact : ∀ x a, K'.operatorAction (σ x) (f a) = f (K.operatorAction x a))
    (hΓ : ∀ x, Γ' (σ x) = f (Γ x)) (x : K.L) (a : A) :
    covariantDerivative K' Γ' (σ x) (f a) = f (covariantDerivative K Γ x a) := by
  simp only [covariantDerivative, hact, hΓ, map_sub, map_add, map_mul]

end InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

end
