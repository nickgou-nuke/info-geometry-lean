/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
import Mathlib.Algebra.Algebra.Equiv

/-!
# Naturality of derivation-based operator geometry

A Lie equivalence transports the derivation directions and an algebra
equivalence transports the coefficients. The explicit intertwining hypothesis
relates their actual actions. One-forms remain native Mathlib linear maps;
the differential and curvature identities are evaluated on transformed
directions, so no replacement two-cochain carrier is introduced.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

open InfoGeometry.Algebra

variable {R A B : Type*} [CommRing R]
variable [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable {K : DerivationLieLane R A} {K' : DerivationLieLane R B}
variable (σ : K.L ≃ₗ⁅R⁆ K'.L) (e : A ≃ₐ[R] B)

/-- Simultaneous transport of the base directions and operator coefficients. -/
def transportOneForm (Γ : OneForm K) : OneForm K' :=
  e.toLinearMap.comp (Γ.comp σ.symm.toLinearMap)

@[simp] theorem transportOneForm_apply (Γ : OneForm K) (x : K'.L) :
    transportOneForm σ e Γ x = e (Γ (σ.symm x)) := rfl

@[simp] theorem transportOneForm_apply_image (Γ : OneForm K) (x : K.L) :
    transportOneForm σ e Γ (σ x) = e (Γ x) := by
  simp only [transportOneForm_apply, LieEquiv.symm_apply_apply]

variable (hρ : ∀ (x : K.L) (a : A),
  K'.operatorAction (σ x) (e a) = e (K.operatorAction x a))

include hρ

/-- The degree-zero differential respects the two compatible equivalences. -/
theorem exteriorDerivativeZero_transport (a : A) :
    exteriorDerivativeZero K' (e a) =
      transportOneForm σ e (exteriorDerivativeZero K a) := by
  apply LinearMap.ext
  intro y
  rw [transportOneForm_apply, exteriorDerivativeZero_apply,
    exteriorDerivativeZero_apply]
  simpa only [LieEquiv.apply_symm_apply] using hρ (σ.symm y) a

/-- Naturality includes the Lie bracket term in the CE differential. -/
theorem exteriorDerivativeOne_transport
    (Γ : OneForm K) (x y : K.L) :
    exteriorDerivativeOne K' (transportOneForm σ e Γ) (σ x) (σ y) =
      e (exteriorDerivativeOne K Γ x y) := by
  rw [exteriorDerivativeOne_apply, exteriorDerivativeOne_apply,
    ← σ.map_lie x y]
  simp only [transportOneForm_apply_image, hρ, map_sub]

/-- Curvature transports exactly in the noncommutative coefficient algebra. -/
theorem connectionCurvature_transport
    (Γ : OneForm K) (x y : K.L) :
    connectionCurvature K' (transportOneForm σ e Γ) (σ x) (σ y) =
      e (connectionCurvature K Γ x y) := by
  rw [connectionCurvature_apply, connectionCurvature_apply,
    ← σ.map_lie x y]
  simp only [transportOneForm_apply_image, hρ, map_sub, map_add, map_mul]

/-- The connection-corrected derivation transports on every coefficient. -/
theorem covariantDerivative_transport
    (Γ : OneForm K) (x : K.L) (a : A) :
    covariantDerivative K' (transportOneForm σ e Γ) (σ x) (e a) =
      e (covariantDerivative K Γ x a) := by
  simp only [covariantDerivative, transportOneForm_apply_image, hρ,
    map_sub, map_add, map_mul]

/-- The full Maurer--Cartan equation is invariant under compatible transport. -/
theorem satisfiesMaurerCartan_transport_iff (Γ : OneForm K) :
    SatisfiesMaurerCartan K' (transportOneForm σ e Γ) ↔
      SatisfiesMaurerCartan K Γ := by
  constructor
  · intro h
    change connectionCurvature K' (transportOneForm σ e Γ) = 0 at h
    change connectionCurvature K Γ = 0
    apply DFunLike.ext
    intro x
    apply LinearMap.ext
    intro y
    change connectionCurvature K Γ x y = 0
    apply e.injective
    rw [map_zero, ← connectionCurvature_transport σ e hρ Γ x y, h]
    rfl
  · intro h
    change connectionCurvature K Γ = 0 at h
    change connectionCurvature K' (transportOneForm σ e Γ) = 0
    apply DFunLike.ext
    intro x
    apply LinearMap.ext
    intro y
    change connectionCurvature K' (transportOneForm σ e Γ) x y = 0
    have ht := connectionCurvature_transport σ e hρ Γ (σ.symm x) (σ.symm y)
    rw [LieEquiv.apply_symm_apply, LieEquiv.apply_symm_apply, h] at ht
    change connectionCurvature K' (transportOneForm σ e Γ) x y = e 0 at ht
    exact ht.trans (map_zero e)

end InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
