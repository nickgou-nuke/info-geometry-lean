/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.Complex
import InfoGeometry.Arithmetic.AlpogeDeligneSignOnlyCore

/-!
# Native `ZMod` additive-character specialization of the transfer core

The transfer/Plancherel theorem is stated for a nontrivial additive character.
This leaf instantiates it with Mathlib's standard character on a prime field.
It proves a finite-field Fourier identity; it does not formalize étale
cohomology, weak Lefschetz, or Deligne's geometric weight theorem.
-/

noncomputable section
open scoped BigOperators

namespace InfoGeometry.Arithmetic.AlpogeZModCharacterBridge

open InfoGeometry.Arithmetic.AlpogeDeligneSignOnlyCore

theorem stdZModAddChar_bilinear_plancherel
    {p : ℕ} [Fact p.Prime]
    {A : Type*} [AddCommGroup A] [Module (ZMod p) A] [Fintype A]
    [DecidableEq A]
    (b : A →ₗ[ZMod p] A →ₗ[ZMod p] ZMod p)
    (hb : ∀ y : A, (∀ x : A, b x y = 0) → y = 0)
    {h : ZMod p} (hh : h ≠ 0) (f : A → ℂ) :
    (∑ x : A, ‖∑ y : A,
      ZMod.stdAddChar (h * b x y) * f y‖ ^ 2) =
      (Fintype.card A : ℝ) * ∑ y : A, ‖f y‖ ^ 2 := by
  let ψ : ZMod p → ℂ := ZMod.stdAddChar
  have hψ0 : ψ 0 = 1 := by
    simp [ψ, ZMod.stdAddChar]
  have hψ_add : ∀ x y, ψ (x + y) = ψ x * ψ y := by
    intro x y
    exact (ZMod.stdAddChar (N := p)).map_add_eq_mul x y
  have hψ_ne : ∃ u : ZMod p, ψ u ≠ 1 := by
    refine ⟨1, ?_⟩
    intro h1
    have h10 : (1 : ZMod p) = 0 := by
      apply ZMod.injective_stdAddChar (N := p)
      simpa [ψ, ZMod.stdAddChar] using h1
    exact one_ne_zero h10
  exact fourier_bilinear_plancherel ψ hψ0 hψ_add hψ_ne b hb hh f

end InfoGeometry.Arithmetic.AlpogeZModCharacterBridge

namespace InfoGeometry.Arithmetic.AlpogeFiniteFieldCharacterBridge

open InfoGeometry.Arithmetic.AlpogeDeligneSignOnlyCore

/-- Plancherel for any finite field, using Mathlib's trace-constructed primitive
complex additive character rather than restricting the scalar field to `ZMod p`. -/
theorem primitiveFiniteFieldChar_bilinear_plancherel
    {F : Type*} [Field F] [Fintype F]
    {A : Type*} [AddCommGroup A] [Module F A] [Fintype A] [DecidableEq A]
    (b : A →ₗ[F] A →ₗ[F] F)
    (hb : ∀ y : A, (∀ x : A, b x y = 0) → y = 0)
    {h : F} (hh : h ≠ 0) (f : A → ℂ) :
    (∑ x : A, ‖∑ y : A,
      AddChar.FiniteField.primitiveChar_to_Complex F (h * b x y) * f y‖ ^ 2) =
      (Fintype.card A : ℝ) * ∑ y : A, ‖f y‖ ^ 2 := by
  let ψ : F → ℂ := AddChar.FiniteField.primitiveChar_to_Complex F
  have hψ0 : ψ 0 = 1 := by simp [ψ]
  have hψ_add : ∀ x y, ψ (x + y) = ψ x * ψ y := by
    intro x y
    exact (AddChar.FiniteField.primitiveChar_to_Complex F).map_add_eq_mul x y
  have hprim := AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F
  have hψ_ne : ∃ u : F, ψ u ≠ 1 := by
    have hne : (AddChar.FiniteField.primitiveChar_to_Complex F) ≠ 1 := by
      have hshift := hprim (a := 1) one_ne_zero
      simpa using hshift
    obtain ⟨u, hu⟩ := AddChar.ne_one_iff.mp hne
    exact ⟨u, hu⟩
  exact fourier_bilinear_plancherel ψ hψ0 hψ_add hψ_ne b hb hh f

/-- Dimension form of finite-field Plancherel: the Fourier norm factor is
`|F| ^ dim_F(A)`, exposing the prime-power scale used in Deligne estimates. -/
theorem primitiveFiniteFieldChar_bilinear_plancherel_finrank
    {F : Type*} [Field F] [Fintype F]
    {A : Type*} [AddCommGroup A] [Module F A] [Fintype A] [DecidableEq A]
    [FiniteDimensional F A]
    (b : A →ₗ[F] A →ₗ[F] F)
    (hb : ∀ y : A, (∀ x : A, b x y = 0) → y = 0)
    {h : F} (hh : h ≠ 0) (f : A → ℂ) :
    (∑ x : A, ‖∑ y : A,
      AddChar.FiniteField.primitiveChar_to_Complex F (h * b x y) * f y‖ ^ 2) =
      (Fintype.card F : ℝ) ^ Module.finrank F A * ∑ y : A, ‖f y‖ ^ 2 := by
  rw [primitiveFiniteFieldChar_bilinear_plancherel b hb hh f]
  congr 1
  have hcard :
      (Fintype.card A : ℝ) = (Fintype.card F : ℝ) ^ Module.finrank F A := by
    exact_mod_cast (Module.card_eq_pow_finrank (K := F) (V := A))
  exact hcard

end InfoGeometry.Arithmetic.AlpogeFiniteFieldCharacterBridge
