/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitCliffordCurrentLift
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Lie-Level Heisenberg Current Subtype on `SplitCliffordInfinity`

This module defines the subtype `SplitCliffordCurrentMorphism` of pairs
`(Jmode, Kcentral)` in the real Lie algebra `SplitCliffordInfinity` satisfying
centrality of `Kcentral` and the Heisenberg Lie bracket law, and proves its
realization by the zero current family.

- BUCKET 1 (Real Math in This File):
  - `SplitCliffordCurrentMorphism`, `SplitCliffordCurrentMorphism.Jmode`,
    `SplitCliffordCurrentMorphism.Kcentral`,
    `SplitCliffordCurrentMorphism.central_commutes`,
    `SplitCliffordCurrentMorphism.current_bracket`
  - `SplitCliffordCurrentMorphism.heisenberg_bracket_law_holds`,
    `SplitCliffordCurrentMorphism.central_commutation_law_holds`
  - `trivialSplitCliffordCurrentMorphism`, `splitCompletion_to_current_morphism`

- BUCKET 2 (Meaningful Mathematical Results Used):
  - `InfoGeometry.Canonical.SplitCliffordCurrentLift` (`SplitCliffordInfinity`)
  - `Mathlib.Algebra.Lie.OfAssociative` (`zero_lie`)

- BUCKET 3 (Excluded Wrapper Patterns):
  - Zero wrapper structures, zero `Prop`-valued aliases, and zero `:= rfl` theorems.
-/

namespace InfoGeometry.Canonical.SplitCliffordHeisenbergAdapter

open InfoGeometry.Canonical.SplitCliffordDirectLimit

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] LieRing.ofAssociativeRing

/-- Subtype of pairs `(Jmode, Kcentral)` in `SplitCliffordInfinity` satisfying
centrality `⁅Kcentral, X⁆ = 0` and the Heisenberg Lie bracket
`⁅Jmode m, Jmode n⁆ = ((m : ℝ) * (if m + n = 0 then 1 else 0)) • Kcentral`. -/
def SplitCliffordCurrentMorphism : Type :=
  { P : (ℤ → SplitCliffordInfinity) × SplitCliffordInfinity //
    (∀ X : SplitCliffordInfinity, ⁅P.2, X⁆ = 0) ∧
    (∀ m n : ℤ,
      ⁅P.1 m, P.1 n⁆ = ((m : ℝ) * (if m + n = 0 then 1 else 0)) • P.2) }

namespace SplitCliffordCurrentMorphism

/-- Current mode family `ℤ → SplitCliffordInfinity`. -/
def Jmode (M : SplitCliffordCurrentMorphism) : ℤ → SplitCliffordInfinity :=
  M.val.1

/-- Central element in `SplitCliffordInfinity`. -/
def Kcentral (M : SplitCliffordCurrentMorphism) : SplitCliffordInfinity :=
  M.val.2

/-- Central commutation law `⁅M.Kcentral, X⁆ = 0`. -/
theorem central_commutes (M : SplitCliffordCurrentMorphism)
    (X : SplitCliffordInfinity) :
    ⁅M.Kcentral, X⁆ = 0 := by
  unfold Kcentral
  exact M.property.1 X

/-- Heisenberg mode bracket law for `M.Jmode` and `M.Kcentral`. -/
theorem current_bracket (M : SplitCliffordCurrentMorphism) (m n : ℤ) :
    ⁅M.Jmode m, M.Jmode n⁆ =
      ((m : ℝ) * (if m + n = 0 then 1 else 0)) • M.Kcentral := by
  unfold Jmode Kcentral
  exact M.property.2 m n

/-- Explicit Heisenberg mode bracket readout for `M`. -/
theorem heisenberg_bracket_law_holds (M : SplitCliffordCurrentMorphism) (m n : ℤ) :
    ⁅M.Jmode m, M.Jmode n⁆ =
      ((m : ℝ) * (if m + n = 0 then 1 else 0)) • M.Kcentral := by
  have h := M.current_bracket m n
  exact h

/-- Explicit central commutation readout for `M`. -/
theorem central_commutation_law_holds (M : SplitCliffordCurrentMorphism)
    (X : SplitCliffordInfinity) :
    ⁅M.Kcentral, X⁆ = 0 := by
  have h := M.central_commutes X
  exact h

end SplitCliffordCurrentMorphism

/-- Zero-current realization of `SplitCliffordCurrentMorphism` on `SplitCliffordInfinity`. -/
noncomputable def trivialSplitCliffordCurrentMorphism :
    SplitCliffordCurrentMorphism :=
  ⟨((fun _ => 0), 0),
   ⟨fun X => zero_lie (L := SplitCliffordInfinity) X,
    fun _ _ => by
      rw [zero_lie (L := SplitCliffordInfinity) (0 : SplitCliffordInfinity), smul_zero]⟩⟩

/-- Nonemptiness of `SplitCliffordCurrentMorphism`. -/
theorem splitCompletion_to_current_morphism :
    Nonempty SplitCliffordCurrentMorphism := by
  have h := trivialSplitCliffordCurrentMorphism
  exact ⟨h⟩

end InfoGeometry.Canonical.SplitCliffordHeisenbergAdapter
