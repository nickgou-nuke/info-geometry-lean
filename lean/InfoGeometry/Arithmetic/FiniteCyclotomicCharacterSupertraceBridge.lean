/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Arithmetic.FiniteMobiusFermionSupertraceBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite cyclotomic character supertrace

The Möbius sign and the multiplicative character are separate weights.  This
owner proves their finite subset-product expansion without constructing an
infinite Dirichlet series or an analytic `L`-function, including the
non-commutative `[Ring B]` character-weighted Euler factor expansion.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.FiniteCyclotomicCharacterSupertraceBridge

open scoped BigOperators
open InfoGeometry.Arithmetic.FiniteMobiusFermionSupertraceBridge
open InfoGeometry.Algebra.FiniteSpin

/-- Non-commutativity witness for the finite spin algebra carrier. -/
theorem exists_noncomm_pair :
    ∃ x y : Mat2C, x * y ≠ y * x :=
  ⟨J_plus, J_minus, j_plus_j_minus_ne⟩

section NonCommRingCharacterEulerFactor

variable {B : Type*} [Ring B]

/-- Character-weighted Euler factor `1 - χp * wp` in an arbitrary non-commutative ring `[Ring B]`. -/
def ringCharacterEulerFactor (χp wp : B) : B :=
  1 - χp * wp

/-- Over any non-commutative ring `[Ring B]`, if `w₁` commutes with `χ₂`, then the 2-mode
character-weighted Euler product factors the character product `χ₁ * χ₂` to the left of `w₁ * w₂`. -/
theorem ringCharacterEulerFactor_two_modes
    (χ₁ w₁ χ₂ w₂ : B) (hcomm : Commute w₁ χ₂) :
    ringCharacterEulerFactor χ₁ w₁ * ringCharacterEulerFactor χ₂ w₂ =
      1 - χ₁ * w₁ - χ₂ * w₂ + (χ₁ * χ₂) * (w₁ * w₂) := by
  unfold ringCharacterEulerFactor
  have hprod : (χ₁ * w₁) * (χ₂ * w₂) = (χ₁ * χ₂) * (w₁ * w₂) := by
    calc
      (χ₁ * w₁) * (χ₂ * w₂) = χ₁ * (w₁ * χ₂) * w₂ := by noncomm_ring
      _ = χ₁ * (χ₂ * w₁) * w₂ := by rw [hcomm.eq]
      _ = (χ₁ * χ₂) * (w₁ * w₂) := by noncomm_ring
  calc
    (1 - χ₁ * w₁) * (1 - χ₂ * w₂)
      = 1 - χ₁ * w₁ - χ₂ * w₂ + (χ₁ * w₁) * (χ₂ * w₂) := by noncomm_ring
    _ = 1 - χ₁ * w₁ - χ₂ * w₂ + (χ₁ * χ₂) * (w₁ * w₂) := by rw [hprod]

end NonCommRingCharacterEulerFactor

theorem finite_character_supertrace
    {α : Type*} [CommRing α]
    (P : Finset ℕ) (χ : ℕ → α)
    (hχ_one : χ 1 = 1)
    (hχ_mul : ∀ x y : ℕ, χ (x * y) = χ x * χ y)
    (w : ℕ → α) :
    (∏ p ∈ P, (1 - χ p * w p)) =
      ∑ S ∈ P.powerset,
        (-1 : α) ^ S.card *
          χ (InfoGeometry.Arithmetic.FiniteMobiusFermionSupertraceBridge.primeSquarefreeProduct S) *
          ∏ p ∈ S, w p := by
  rw [← finiteFermionSupertrace_eq_eulerProduct P (fun p => χ p * w p)]
  unfold finiteFermionSupertrace
  have hχprod : ∀ S : Finset ℕ,
      χ (InfoGeometry.Arithmetic.FiniteMobiusFermionSupertraceBridge.primeSquarefreeProduct S) =
        ∏ p ∈ S, χ p := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        simpa [InfoGeometry.Arithmetic.FiniteMobiusFermionSupertraceBridge.primeSquarefreeProduct]
          using hχ_one
    | @insert p S hp ih =>
        simp only [InfoGeometry.Arithmetic.FiniteMobiusFermionSupertraceBridge.primeSquarefreeProduct,
          Finset.prod_insert hp]
        rw [hχ_mul]
        have ih' : χ (∏ q ∈ S, q) = ∏ q ∈ S, χ q := by
          simpa [primeSquarefreeProduct] using ih
        rw [ih']
  refine Finset.sum_congr rfl ?_
  intro S hS
  rw [Finset.prod_mul_distrib, hχprod S]
  ring

theorem finite_character_mobius_supertrace
    {α : Type*} [CommRing α]
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (χ : ℕ → α) (w : ℕ → α)
    (hχ_one : χ 1 = 1)
    (hχ_mul : ∀ x y : ℕ, χ (x * y) = χ x * χ y) :
    (∏ p ∈ P, (1 - χ p * w p)) =
      ∑ S ∈ P.powerset,
        ((ArithmeticFunction.moebius (primeSquarefreeProduct S) : ℤ) : α) *
          χ (primeSquarefreeProduct S) * ∏ p ∈ S, w p := by
  rw [finite_character_supertrace P χ hχ_one hχ_mul w]
  refine Finset.sum_congr rfl ?_
  intro S hS
  have hSub : S ⊆ P := Finset.mem_powerset.mp hS
  have hμ :
      ArithmeticFunction.moebius (primeSquarefreeProduct S) = (-1 : ℤ) ^ S.card :=
    InfoGeometry.Arithmetic.PrimeBitWittenIndex.mobius_prime_product_eq_parity S
      (fun p hp => hP p (hSub hp))
  rw [hμ]
  push_cast
  ring

theorem finite_character_supertrace_monoidHom
    {α : Type*} [CommRing α]
    (P : Finset ℕ) (χ : ℕ →* α) (w : ℕ → α) :
    (∏ p ∈ P, (1 - χ p * w p)) =
      ∑ S ∈ P.powerset,
        (-1 : α) ^ S.card * χ (primeSquarefreeProduct S) *
          ∏ p ∈ S, w p := by
  exact finite_character_supertrace P χ χ.map_one χ.map_mul w

theorem finite_character_mobius_supertrace_monoidHom
    {α : Type*} [CommRing α]
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (χ : ℕ →* α) (w : ℕ → α) :
    (∏ p ∈ P, (1 - χ p * w p)) =
      ∑ S ∈ P.powerset,
        ((ArithmeticFunction.moebius (primeSquarefreeProduct S) : ℤ) : α) *
          χ (primeSquarefreeProduct S) * ∏ p ∈ S, w p := by
  exact finite_character_mobius_supertrace P hP χ w χ.map_one χ.map_mul

end InfoGeometry.Arithmetic.FiniteCyclotomicCharacterSupertraceBridge
