/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.DerivationGeometryHomTransport

/-!
# Homomorphic transport of the degree-two covariant differential

The map of coefficients need only be an algebra homomorphism. The theorem
states equality on mapped directions, without asserting extension or
surjectivity of cochains.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

open InfoGeometry.Algebra

variable {R A B : Type*} [CommRing R]
variable [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable {K : DerivationLieLane R A} {K' : DerivationLieLane R B}

/-- The degree-two CE differential respects compatible source and target
cochains, including all three Lie-bracket terms. -/
theorem exteriorDerivativeTwo_hom_apply
    (σ : K.L →ₗ⁅R⁆ K'.L) (f : A →ₐ[R] B)
    (F : TwoForm K) (F' : TwoForm K')
    (hact : ∀ x a, K'.operatorAction (σ x) (f a) = f (K.operatorAction x a))
    (hF : ∀ x y, F' (σ x) (σ y) = f (F x y)) (x y z : K.L) :
    exteriorDerivativeTwo K' F' (σ x) (σ y) (σ z) =
      f (exteriorDerivativeTwo K F x y z) := by
  rw [exteriorDerivativeTwo_apply, exteriorDerivativeTwo_apply,
    ← σ.map_lie, ← σ.map_lie, ← σ.map_lie]
  simp only [hF, hact, map_add, map_sub]

/-- The covariant degree-two differential is natural on mapped directions. -/
theorem covariantExteriorDerivativeTwo_hom_apply
    (σ : K.L →ₗ⁅R⁆ K'.L) (f : A →ₐ[R] B)
    (Γ : OneForm K) (Γ' : OneForm K') (F : TwoForm K) (F' : TwoForm K')
    (hact : ∀ x a, K'.operatorAction (σ x) (f a) = f (K.operatorAction x a))
    (hΓ : ∀ x, Γ' (σ x) = f (Γ x))
    (hF : ∀ x y, F' (σ x) (σ y) = f (F x y)) (x y z : K.L) :
    covariantExteriorDerivativeTwo K' Γ' F' (σ x) (σ y) (σ z) =
      f (covariantExteriorDerivativeTwo K Γ F x y z) := by
  unfold covariantExteriorDerivativeTwo
  rw [exteriorDerivativeTwo_hom_apply σ f F F' hact hF]
  simp only [hΓ, hF, map_add, map_sub, map_mul]

/-- Curvature and its covariant differential transport together under the
same compatible pair of homomorphisms. -/
theorem connectionBianchi_hom_apply
    (σ : K.L →ₗ⁅R⁆ K'.L) (f : A →ₐ[R] B)
    (Γ : OneForm K) (Γ' : OneForm K')
    (hact : ∀ x a, K'.operatorAction (σ x) (f a) = f (K.operatorAction x a))
    (hΓ : ∀ x, Γ' (σ x) = f (Γ x)) (x y z : K.L) :
    covariantExteriorDerivativeTwo K' Γ' (connectionCurvature K' Γ')
        (σ x) (σ y) (σ z) =
      f (covariantExteriorDerivativeTwo K Γ (connectionCurvature K Γ) x y z) := by
  apply covariantExteriorDerivativeTwo_hom_apply σ f Γ Γ' _ _ hact hΓ
  intro u v
  exact connectionCurvature_hom_apply σ f Γ Γ' hact hΓ u v

end InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

end
