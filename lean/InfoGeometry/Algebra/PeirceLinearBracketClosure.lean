/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Peirce operator closure for a commutator

This owner records the purely associative statement about endomorphisms that
is used when a Peirce decomposition is already available.  It does not claim
that an octonion derivation carrier has a five-grading; that extra statement
requires a separate, concrete derivation model.
-/

set_option linter.unusedSimpArgs false

namespace InfoGeometry.Algebra.PeirceLinearBracketClosure

open InfoGeometry.Algebra.FiniteSpin

/-- Non-commutativity witness for the finite spin algebra carrier. -/
theorem exists_noncomm_pair :
    ∃ x y : Mat2C, x * y ≠ y * x :=
  ⟨J_plus, J_minus, j_plus_j_minus_ne⟩

section NonCommRingPeirceBracketClosure

variable {B : Type*} [Ring B]

/-- Associative commutator `[X, Y] = X * Y - Y * X` in a non-commutative ring `[Ring B]`. -/
def ringLieBracket (X Y : B) : B :=
  X * Y - Y * X

/-- Over any non-commutative ring `[Ring B]`, if `Dplus` lies in the `+1` Peirce corner
(`Dplus * Pplus = 0` and `Pminus * Dplus = 0`) and `Dminus` lies in the `-1` Peirce corner
(`Dminus * Pminus = 0` and `Pplus * Dminus = 0`), then their commutator `ringLieBracket Dplus Dminus`
has vanishing off-diagonal Peirce corners `Pminus * [Dplus, Dminus] * Pplus = 0` and
`Pplus * [Dplus, Dminus] * Pminus = 0`. -/
theorem ringLieBracket_peirce_g0_closure
    (Pplus Pminus Dplus Dminus : B)
    (hplus_right : Dplus * Pplus = 0)
    (hplus_left : Pminus * Dplus = 0)
    (hminus_right : Dminus * Pminus = 0)
    (hminus_left : Pplus * Dminus = 0) :
    Pminus * ringLieBracket Dplus Dminus * Pplus = 0 ∧
      Pplus * ringLieBracket Dplus Dminus * Pminus = 0 := by
  constructor
  · dsimp [ringLieBracket]
    have h1 : Pminus * (Dplus * Dminus - Dminus * Dplus) * Pplus =
        (Pminus * Dplus) * Dminus * Pplus - Pminus * Dminus * (Dplus * Pplus) := by
      noncomm_ring
    rw [h1, hplus_left, hplus_right, zero_mul, zero_mul, mul_zero, sub_self]
  · dsimp [ringLieBracket]
    have h2 : Pplus * (Dplus * Dminus - Dminus * Dplus) * Pminus =
        Pplus * Dplus * (Dminus * Pminus) - (Pplus * Dminus) * Dplus * Pminus := by
      noncomm_ring
    rw [h2, hminus_right, hminus_left, mul_zero, zero_mul, zero_mul, sub_self]

end NonCommRingPeirceBracketClosure

variable {R Carrier : Type*} [CommRing R]
variable [AddCommGroup Carrier] [Module R Carrier]

abbrev Endomorphism (R Carrier : Type*) [CommRing R]
    [AddCommGroup Carrier] [Module R Carrier] := Carrier →ₗ[R] Carrier

def lieBracket (D₁ D₂ : Endomorphism R Carrier) : Endomorphism R Carrier :=
  D₁.comp D₂ - D₂.comp D₁

def g0Submodule (Deriv : Submodule R (Endomorphism R Carrier))
    (Pplus Pminus : Endomorphism R Carrier) :
    Submodule R (Endomorphism R Carrier) where
  carrier := {D | D ∈ Deriv ∧ (Pminus.comp D).comp Pplus = 0 ∧
    (Pplus.comp D).comp Pminus = 0}
  zero_mem' := by simp
  add_mem' := by
    intro D E hD hE
    exact ⟨Deriv.add_mem hD.1 hE.1,
      by rw [LinearMap.comp_add, LinearMap.add_comp, hD.2.1, hE.2.1,
        add_zero],
      by rw [LinearMap.comp_add, LinearMap.add_comp, hD.2.2, hE.2.2,
        add_zero]⟩
  smul_mem' := by
    intro c D hD
    exact ⟨Deriv.smul_mem c hD.1,
      by rw [LinearMap.comp_smul, LinearMap.smul_comp, hD.2.1,
        smul_zero],
      by rw [LinearMap.comp_smul, LinearMap.smul_comp, hD.2.2,
        smul_zero]⟩

def memGPlus1 (Deriv : Submodule R (Endomorphism R Carrier))
    (Pplus Pminus D : Endomorphism R Carrier) : Prop :=
  D ∈ Deriv ∧ D.comp Pplus = 0 ∧ Pminus.comp D = 0

def memGMinus1 (Deriv : Submodule R (Endomorphism R Carrier))
    (Pplus Pminus D : Endomorphism R Carrier) : Prop :=
  D ∈ Deriv ∧ D.comp Pminus = 0 ∧ Pplus.comp D = 0

theorem lieBracket_mem_g0
    (Deriv : Submodule R (Endomorphism R Carrier))
    (Pplus Pminus : Endomorphism R Carrier)
    (hBracket : ∀ D₁ D₂ : Endomorphism R Carrier, D₁ ∈ Deriv → D₂ ∈ Deriv →
      lieBracket D₁ D₂ ∈ Deriv)
    {Dplus Dminus : Endomorphism R Carrier}
    (hplus : memGPlus1 Deriv Pplus Pminus Dplus)
    (hminus : memGMinus1 Deriv Pplus Pminus Dminus) :
    lieBracket Dplus Dminus ∈ g0Submodule Deriv Pplus Pminus := by
  refine ⟨hBracket Dplus Dminus hplus.1 hminus.1, ?_, ?_⟩
  · rw [show (Pminus.comp (lieBracket Dplus Dminus)).comp Pplus =
      (Pminus.comp Dplus).comp (Dminus.comp Pplus) -
        (Pminus.comp Dminus).comp (Dplus.comp Pplus) by
        simp [lieBracket, LinearMap.comp_sub, LinearMap.sub_comp,
          LinearMap.comp_assoc]]
    simp only [LinearMap.comp_assoc, hplus.2.2, hplus.2.1,
      LinearMap.zero_comp, LinearMap.comp_zero, sub_zero]
  · rw [show (Pplus.comp (lieBracket Dplus Dminus)).comp Pminus =
      (Pplus.comp Dplus).comp (Dminus.comp Pminus) -
        (Pplus.comp Dminus).comp (Dplus.comp Pminus) by
        simp [lieBracket, LinearMap.comp_sub, LinearMap.sub_comp,
          LinearMap.comp_assoc]]
    simp only [LinearMap.comp_assoc, hminus.2.2, hminus.2.1,
      LinearMap.zero_comp, LinearMap.comp_zero, sub_zero]

end InfoGeometry.Algebra.PeirceLinearBracketClosure
