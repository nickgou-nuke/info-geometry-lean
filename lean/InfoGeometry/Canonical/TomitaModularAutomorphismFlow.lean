/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.InnerProductSpace.Basic

noncomputable section

namespace InfoGeometry.Canonical.TomitaModularAutomorphismFlow

/-!
# Abstract Unitary-Conjugation Automorphism Flow Interface

Given a supplied one-parameter unitary group `MUG : ModularUnitaryGroup H` on a
complex inner-product space `H`, this module defines the conjugation flow
`modularFlow MUG t A = U(t) ∘ A ∘ U(-t)` on bounded linear operators `H →L[ℂ] H`,
proving:
1. Identity flow at `t = 0`: `σ₀(A) = A`
2. Multiplicative composition law: `σ_t(A ∘ B) = σ_t(A) ∘ σ_t(B)`
3. Additive one-parameter law: `σ_{t1 + t2}(A) = σ_{t1}(σ_{t2}(A))` and inverse laws
4. Norm transport along the unitary orbit

This file does **not** construct the modular operator `Δ` from a state or prove
KMS invariance: `kms_state_modular_flow_product` applies any function `omega` to
`modularFlow_mul`, and `ModularInvariantState` takes invariance as a structure field.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Abstract one-parameter unitary group interface `U : ℝ → (H ≃ₗᵢ[ℂ] H)` (used to model `Δ^(it)`). -/
structure ModularUnitaryGroup (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  U : ℝ → (H ≃ₗᵢ[ℂ] H)
  map_zero : U 0 = LinearIsometryEquiv.refl ℂ H
  map_add : ∀ t1 t2 : ℝ, U (t1 + t2) = (U t2).trans (U t1)
  inv_cancel : ∀ (t : ℝ) (y : H), U (-t) (U t y) = y

/-- Conjugation flow `σ_t(A) = U(t) ∘ A ∘ U(-t)` on `H →L[ℂ] H`. -/
def modularFlow (MUG : ModularUnitaryGroup H) (t : ℝ) (A : H →L[ℂ] H) : H →L[ℂ] H :=
  (MUG.U t : H →L[ℂ] H).comp (A.comp (MUG.U (-t) : H →L[ℂ] H))

/-- **Theorem**: Identity flow at t = 0: σ₀(A) = A. -/
theorem modularFlow_zero (MUG : ModularUnitaryGroup H) (A : H →L[ℂ] H) :
    modularFlow MUG 0 A = A := by
  dsimp [modularFlow]
  have h0 : - (0 : ℝ) = 0 := neg_zero
  rw [h0, MUG.map_zero]
  ext x
  rfl

/-- **Theorem**: Multiplicative property of modular flow: σ_t(A B) = σ_t(A) σ_t(B). -/
theorem modularFlow_mul (MUG : ModularUnitaryGroup H) (t : ℝ) (A B : H →L[ℂ] H) :
    modularFlow MUG t (A.comp B) = (modularFlow MUG t A).comp (modularFlow MUG t B) := by
  ext x
  dsimp [modularFlow]
  change MUG.U t (A (B (MUG.U (-t) x))) = MUG.U t (A (MUG.U (-t) (MUG.U t (B (MUG.U (-t) x)))))
  rw [MUG.inv_cancel t]

/-- **Theorem**: Composition property of modular flow: σ_{t1 + t2}(A) = σ_{t1}(σ_{t2}(A)). -/
theorem modularFlow_add (MUG : ModularUnitaryGroup H) (t1 t2 : ℝ) (A : H →L[ℂ] H) :
    modularFlow MUG (t1 + t2) A = modularFlow MUG t1 (modularFlow MUG t2 A) := by
  ext x
  dsimp [modularFlow]
  have h_neg : - (t1 + t2) = -t2 + -t1 := by ring
  rw [MUG.map_add t1 t2, h_neg, MUG.map_add (-t2) (-t1)]
  rfl

/-- Congruence under any readout `omega : (H →L[ℂ] H) → ℂ` applied to `modularFlow_mul`. -/
theorem kms_state_modular_flow_product (MUG : ModularUnitaryGroup H) (t : ℝ)
    (omega : (H →L[ℂ] H) → ℂ) (A B : H →L[ℂ] H) :
    omega (modularFlow MUG t (A.comp B)) = omega ((modularFlow MUG t A).comp (modularFlow MUG t B)) := by
  rw [modularFlow_mul]

/-- The modular flow has an explicit inverse at every time. -/
theorem modularFlow_neg_left (MUG : ModularUnitaryGroup H) (t : ℝ)
    (A : H →L[ℂ] H) :
    modularFlow MUG (-t) (modularFlow MUG t A) = A := by
  have h := modularFlow_add MUG (-t) t A
  have hzero : -t + t = 0 := by ring
  rw [hzero] at h
  exact h.symm.trans (modularFlow_zero MUG A)

/-- The inverse identity also holds with the two time directions exchanged. -/
theorem modularFlow_neg_right (MUG : ModularUnitaryGroup H) (t : ℝ)
    (A : H →L[ℂ] H) :
    modularFlow MUG t (modularFlow MUG (-t) A) = A := by
  have h := modularFlow_add MUG t (-t) A
  have hzero : t + -t = 0 := by ring
  rw [hzero] at h
  exact h.symm.trans (modularFlow_zero MUG A)

/-- Conjugation transports the operator norm pointwise along the unitary orbit. -/
theorem modularFlow_apply_unitary_norm (MUG : ModularUnitaryGroup H) (t : ℝ)
    (A : H →L[ℂ] H) (x : H) :
    ‖modularFlow MUG t A (MUG.U t x)‖ = ‖A x‖ := by
  dsimp [modularFlow]
  rw [MUG.inv_cancel t]
  exact (MUG.U t).norm_map _

/-- Readout functional paired with an explicit `invariant` hypothesis under `modularFlow MUG`. -/
structure ModularInvariantState (MUG : ModularUnitaryGroup H) where
  omega : (H →L[ℂ] H) → ℂ
  invariant : ∀ t : ℝ, ∀ A : H →L[ℂ] H,
    omega (modularFlow MUG t A) = omega A

/-- Projects the supplied invariance hypothesis `S.invariant` at `(t, A)`. -/
theorem modularFlow_state_invariant
    (MUG : ModularUnitaryGroup H)
    (S : ModularInvariantState MUG)
    (t : ℝ) (A : H →L[ℂ] H) :
    S.omega (modularFlow MUG t A) = S.omega A := by
  exact S.invariant t A

/-- Projects the supplied invariance hypothesis `S.invariant` onto `A.comp B`. -/
theorem modularFlow_product_state_invariant
    (MUG : ModularUnitaryGroup H)
    (S : ModularInvariantState MUG)
    (t : ℝ) (A B : H →L[ℂ] H) :
    S.omega (modularFlow MUG t (A.comp B)) = S.omega (A.comp B) := by
  exact S.invariant t (A.comp B)

end InfoGeometry.Canonical.TomitaModularAutomorphismFlow
