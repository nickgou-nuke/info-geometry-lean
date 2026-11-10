/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitCliffordHeisenbergBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitCliffordInfiniteCurrent
import InfoGeometry.Canonical.SplitCliffordSourceCurrentWick

/-!
# Split-Clifford Source Heisenberg Packaging and Charged-Fock Readouts

This module packages endomorphism-valued current families satisfying eventual
truncation and `SplitSourceEndWickLaw` into `SplitCliffordHeisenbergWitness`,
extracts the concrete charged-Fock truncation and Wick commutator laws, and
exposes the external infinite-current Lie brackets.

- BUCKET 1 (Real Math in This File):
- `packagedHeisenbergWitness`
- `truncLift_of_represented_current`, `wickLift_of_represented_current`,
  `strictWitness_of_represented_current`
- `truncLift_of_splitCurrentLiftDatum`
- `canonicalInfiniteCurrent_commutator_readout`,
  `canonicalInfiniteCurrent_one_negOne`, `canonicalInfiniteCurrent_central`

- BUCKET 2 (Meaningful Mathematical Results Used):
- `InfoGeometry.Canonical.SplitCliffordHeisenbergBridge`
- `InfoGeometry.Canonical.SplitCliffordSourceCurrentWick`
- `InfoGeometry.Canonical.SplitCliffordInfiniteCurrent`

- BUCKET 3 (Excluded Wrapper Patterns):
- Zero wrapper structures, zero `Prop`-valued aliases, and zero `:= rfl` theorems.
-/

namespace InfoGeometry.Canonical.SplitCliffordSourceHeisenberg

open Filter
open InfoGeometry.Canonical.SplitCliffordSourceCurrentWick
open InfoGeometry.Canonical.SplitCliffordHeisenbergBridge
open InfoGeometry.Canonical.SplitCliffordInfiniteCurrent
open InfoGeometry.Canonical.SplitCliffordSourceCurrent

/-- Construct a `SplitCliffordHeisenbergWitness 𝕜 V` from a current family `Jlift`
with eventual positive-mode truncation and `SplitSourceEndWickLaw`. -/
def packagedHeisenbergWitness
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (Jlift : Int → V →ₗ[𝕜] V)
    (hTruncLift : ∀ v : V, ∀ᶠ l : Int in atTop, Jlift l v = 0)
    (hCommLift : SplitSourceEndWickLaw Jlift) :
    SplitCliffordHeisenbergWitness 𝕜 V :=
  ⟨Jlift, hTruncLift, hCommLift⟩

/-- Existence of a locally truncated current family on `ChargedFockSpace 𝕜 α`. -/
theorem truncLift_of_represented_current
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ∃ J :
        Int →
          VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
            VirasoroProject.ChargedFockSpace 𝕜 α,
      ∀ v, ∀ᶠ n : Int in Filter.atTop, J n v = 0 := by
  rcases represented_current_commutator_chargedFock (𝕜 := 𝕜) α with ⟨J, htrunc, _⟩
  exact ⟨J, htrunc⟩

/-- Existence of a current family on `ChargedFockSpace 𝕜 α` satisfying
`SplitSourceEndWickLaw`. -/
theorem wickLift_of_represented_current
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ∃ J :
        Int →
          VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
            VirasoroProject.ChargedFockSpace 𝕜 α,
      SplitSourceEndWickLaw J := by
  rcases represented_current_commutator_chargedFock (𝕜 := 𝕜) α with ⟨J, _, hwick⟩
  exact ⟨J, hwick⟩

/-- Existence of a current family on `ChargedFockSpace 𝕜 α` satisfying both
eventual positive-mode truncation and `SplitSourceEndWickLaw`. -/
theorem strictWitness_of_represented_current
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ∃ J :
        Int →
          VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
            VirasoroProject.ChargedFockSpace 𝕜 α,
      (∀ v, ∀ᶠ n : Int in Filter.atTop, J n v = 0) ∧
        SplitSourceEndWickLaw J := by
  rcases represented_current_commutator_chargedFock (𝕜 := 𝕜) α with
    ⟨J, hTruncLift, hCommLift⟩
  exact ⟨J, hTruncLift, hCommLift⟩

universe u

/-- Eventual positive-mode truncation of the lifted mode family `L.Jlift` for any
`SplitCurrentLiftDatum`. -/
theorem truncLift_of_splitCurrentLiftDatum
    {𝕜 V : Type u} [CommRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (L : SplitCliffordSourceCurrent.SplitCurrentLiftDatum (𝕜 := 𝕜) (V := V)) :
    ∀ v : V, ∀ᶠ l : Int in atTop, L.Jlift l v = 0 := by
  intro v
  exact L.trunc v

/-- Mode commutator identity for the canonical infinite current `Jinf 𝕜`. -/
theorem canonicalInfiniteCurrent_commutator_readout
    (𝕜 : Type*) [CommRing 𝕜]
    (m n : Int) :
    ⁅Jinf 𝕜 m, Jinf 𝕜 n⁆ =
      if m + n = 0 then (m : 𝕜) • Kinf 𝕜 else 0 := by
  have h := canonicalInfiniteCurrent_lie (𝕜 := 𝕜) m n
  exact h

/-- Fundamental mode pair commutator `⁅Jinf 𝕜 1, Jinf 𝕜 (-1)⁆ = (1 : 𝕜) • Kinf 𝕜`. -/
theorem canonicalInfiniteCurrent_one_negOne
    (𝕜 : Type*) [CommRing 𝕜] :
    ⁅Jinf 𝕜 1, Jinf 𝕜 (-1)⁆ = (1 : 𝕜) • Kinf 𝕜 := by
  have h := canonicalInfiniteCurrent_lie_one_neg_one (𝕜 := 𝕜)
  exact h

/-- Centrality of `Kinf 𝕜` in `InfiniteCurrentAlg 𝕜`. -/
theorem canonicalInfiniteCurrent_central
    (𝕜 : Type*) [CommRing 𝕜]
    (Z : InfiniteCurrentAlg 𝕜) :
    ⁅Kinf 𝕜, Z⁆ = 0 := by
  have h := canonicalInfiniteCurrent_lie_central (𝕜 := 𝕜) Z
  exact h

end InfoGeometry.Canonical.SplitCliffordSourceHeisenberg
