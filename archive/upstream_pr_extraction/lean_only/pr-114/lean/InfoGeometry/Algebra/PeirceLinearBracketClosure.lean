/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib

/-!
# Peirce operator closure for a commutator

This owner records the purely associative statement about endomorphisms that
is used when a Peirce decomposition is already available.  It does not claim
that an octonion derivation carrier has a five-grading; that extra statement
requires a separate, concrete derivation model.
-/

namespace InfoGeometry.Algebra.PeirceLinearBracketClosure

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
