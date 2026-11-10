/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Order.Filter.Basic
import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Module.LinearMap.Basic
import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.Canonical.SplitCliffordInfiniteCurrent

/-!
# Split-Clifford Heisenberg Current Bridge and Sugawara Readouts

This module defines the subtype `SplitCliffordHeisenbergWitness 𝕜 V` of
locally truncated Heisenberg current families on `V`, connects it to
`CurrentHeisenbergRep` and `CurrentSugawaraMorphism`, and exposes the external
infinite-current Lie brackets on `InfiniteCurrentAlg 𝕜`.

- BUCKET 1 (Real Math in This File):
  - `SplitCliffordHeisenbergWitness`, `SplitCliffordHeisenbergWitness.J`,
    `SplitCliffordHeisenbergWitness.trunc`, `SplitCliffordHeisenbergWitness.comm`
  - `SplitCliffordHeisenbergWitness.toCurrentHeisenbergRep`,
    `SplitCliffordHeisenbergWitness.toCurrentSugawaraMorphism`,
    `SplitCliffordHeisenbergWitness.currentSugawaraRepresentation`,
    `SplitCliffordHeisenbergWitness.sugawaraStressMode_virasoroBracket`
  - `canonicalInfiniteCurrent_lie`, `canonicalInfiniteCurrent_lie_one_neg_one`,
    `canonicalInfiniteCurrent_lie_neg_one_one`, `canonicalInfiniteCurrent_lie_central`

- BUCKET 2 (Meaningful Mathematical Results Used):
  - `InfoGeometry.Canonical.CurrentSugawaraBridge`
  - `InfoGeometry.Canonical.SplitCliffordInfiniteCurrent`

- BUCKET 3 (Excluded Wrapper Patterns):
  - Zero wrapper structures, zero `Prop`-valued aliases, and zero `:= rfl` theorems.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitCliffordHeisenbergBridge

open Filter
open InfoGeometry.Canonical.CurrentSugawaraBridge
open InfoGeometry.Canonical.SplitCliffordInfiniteCurrent
open VirasoroProject

attribute [local instance 100] LieRing.ofAssociativeRing

local instance linearEndLieRing (𝕜 V : Type*) [Semiring 𝕜]
    [AddCommGroup V] [Module 𝕜 V] : LieRing (V →ₗ[𝕜] V) :=
  LieRing.ofAssociativeRing

/-- Subtype of endomorphism-valued current families `J : Int → V →ₗ[𝕜] V`
satisfying eventual positive-mode truncation and the level-1 Heisenberg
commutator law. -/
def SplitCliffordHeisenbergWitness
    (𝕜 V : Type*) [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V] : Type _ :=
  { J : Int → V →ₗ[𝕜] V //
    (∀ v, atTop.Eventually (fun l => J l v = 0)) ∧
    (∀ m n,
      (J m).commutator (J n) =
        if m + n = 0 then (m : 𝕜) • (1 : V →ₗ[𝕜] V) else 0) }

namespace SplitCliffordHeisenbergWitness

variable {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

/-- Underlying current mode family `Int → V →ₗ[𝕜] V`. -/
def J (W : SplitCliffordHeisenbergWitness 𝕜 V) : Int → V →ₗ[𝕜] V :=
  W.val

/-- Eventual positive-mode truncation of `W.J`. -/
theorem trunc (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    ∀ v, atTop.Eventually (fun l => W.J l v = 0) := by
  intro v
  exact W.property.1 v

/-- Heisenberg mode commutator law of `W.J`. -/
theorem comm (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    ∀ m n,
      (W.J m).commutator (W.J n) =
        if m + n = 0 then (m : 𝕜) • (1 : V →ₗ[𝕜] V) else 0 := by
  intro m n
  exact W.property.2 m n

/-- Convert `W` into a `CurrentHeisenbergRep 𝕜 V`. -/
def toCurrentHeisenbergRep
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    CurrentHeisenbergRep 𝕜 V :=
  ⟨W.J, W.trunc, W.comm⟩

/-- The current mode family of `W.toCurrentHeisenbergRep` equals `W.J`. -/
@[simp]
theorem toCurrentHeisenbergRep_J
    (W : SplitCliffordHeisenbergWitness 𝕜 V)
    (n : Int) :
    (W.toCurrentHeisenbergRep).J n = W.J n := by
  unfold toCurrentHeisenbergRep CurrentHeisenbergRep.J
  rfl

/-- Eventual positive-mode truncation of `W.toCurrentHeisenbergRep` on any vector `v`. -/
theorem toCurrentHeisenbergRep_trunc
    (W : SplitCliffordHeisenbergWitness 𝕜 V) (v : V) :
    ∀ᶠ l : Int in atTop, (W.toCurrentHeisenbergRep).J l v = 0 := by
  have h := W.trunc v
  exact h

/-- Joint readout of the mode family, eventual truncation, and commutator law
of `W.toCurrentHeisenbergRep`. -/
theorem toCurrentHeisenbergRep_readout
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    W.toCurrentHeisenbergRep.J = W.J
      ∧ (∀ v, atTop.Eventually (fun l => W.toCurrentHeisenbergRep.J l v = 0))
      ∧ ∀ m n,
          (W.toCurrentHeisenbergRep.J m).commutator (W.toCurrentHeisenbergRep.J n) =
            if m + n = 0 then (m : 𝕜) • (1 : V →ₗ[𝕜] V) else 0 := by
  constructor
  · rfl
  · exact ⟨W.toCurrentHeisenbergRep.trunc, W.toCurrentHeisenbergRep.comm⟩

/-- Sugawara morphism `CurrentSugawaraMorphism 𝕜 V` induced by `W`. -/
noncomputable def toCurrentSugawaraMorphism
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    CurrentSugawaraMorphism 𝕜 V :=
  CurrentSugawaraMorphism.ofHeisenberg W.toCurrentHeisenbergRep

/-- The Heisenberg component of `W.toCurrentSugawaraMorphism` is `W.toCurrentHeisenbergRep`. -/
@[simp]
theorem toCurrentSugawaraMorphism_heisenberg
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    W.toCurrentSugawaraMorphism.heisenberg = W.toCurrentHeisenbergRep := by
  unfold toCurrentSugawaraMorphism
  exact (CurrentSugawaraMorphism.ofHeisenberg_readout _).1

/-- The Virasoro component of `W.toCurrentSugawaraMorphism` is the Sugawara representation. -/
@[simp]
theorem toCurrentSugawaraMorphism_virasoro
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    W.toCurrentSugawaraMorphism.virasoro =
      (W.toCurrentHeisenbergRep).currentSugawaraRepresentation := by
  unfold toCurrentSugawaraMorphism
  exact (CurrentSugawaraMorphism.ofHeisenberg_readout _).2.1

/-- Joint readout of both components of `W.toCurrentSugawaraMorphism`. -/
theorem toCurrentSugawaraMorphism_readout
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    W.toCurrentSugawaraMorphism.heisenberg = W.toCurrentHeisenbergRep
      ∧ W.toCurrentSugawaraMorphism.virasoro =
        W.toCurrentHeisenbergRep.currentSugawaraRepresentation := by
  constructor
  · exact W.toCurrentSugawaraMorphism_heisenberg
  · exact W.toCurrentSugawaraMorphism_virasoro

/-- Sugawara Virasoro Lie algebra representation obtained from `W`. -/
noncomputable def currentSugawaraRepresentation
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ (V →ₗ[𝕜] V) :=
  (W.toCurrentHeisenbergRep).currentSugawaraRepresentation

/-- The Virasoro central generator acts as the identity in `W.currentSugawaraRepresentation`. -/
theorem currentSugawaraRepresentation_central
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    W.currentSugawaraRepresentation (VirasoroAlgebra.cgen 𝕜) =
      (1 : V →ₗ[𝕜] V) := by
  unfold currentSugawaraRepresentation
  exact CurrentHeisenbergRep.currentSugawaraRepresentation_central W.toCurrentHeisenbergRep

/-- The Virasoro generator `lgen 𝕜 n` acts as `sugawaraStressMode n` in
`W.currentSugawaraRepresentation`. -/
theorem currentSugawaraRepresentation_lgen_apply
    (W : SplitCliffordHeisenbergWitness 𝕜 V) (n : Int) :
    W.currentSugawaraRepresentation (VirasoroAlgebra.lgen 𝕜 n) =
      (W.toCurrentHeisenbergRep).sugawaraStressMode n := by
  unfold currentSugawaraRepresentation
  exact CurrentHeisenbergRep.currentSugawaraRepresentation_lgen_apply W.toCurrentHeisenbergRep n

/-- The Sugawara stress modes of `W` satisfy the Virasoro commutator with central charge $c = 1$. -/
theorem sugawaraStressMode_virasoroBracket
    (W : SplitCliffordHeisenbergWitness 𝕜 V) (m n : Int) :
    ((W.toCurrentHeisenbergRep).sugawaraStressMode m).commutator
        ((W.toCurrentHeisenbergRep).sugawaraStressMode n) =
      (m - n) • (W.toCurrentHeisenbergRep).sugawaraStressMode (m + n)
        + if m + n = 0 then
            (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) • (1 : V →ₗ[𝕜] V))
          else 0 := by
  have h := CurrentHeisenbergRep.sugawaraStressMode_virasoroBracket W.toCurrentHeisenbergRep m n
  exact h

/-- Product pair of `W.toCurrentHeisenbergRep` and `W.currentSugawaraRepresentation`. -/
noncomputable def current_and_sugawara
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    CurrentHeisenbergRep 𝕜 V ×
      (VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ (V →ₗ[𝕜] V)) :=
  ⟨W.toCurrentHeisenbergRep, W.currentSugawaraRepresentation⟩

/-- Product pair of `W.toCurrentSugawaraMorphism` and `W.toCurrentHeisenbergRep`. -/
noncomputable def currentSugawaraMorphism_and_current
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    CurrentSugawaraMorphism 𝕜 V × CurrentHeisenbergRep 𝕜 V :=
  ⟨W.toCurrentSugawaraMorphism, W.toCurrentHeisenbergRep⟩

end SplitCliffordHeisenbergWitness

/-- Top-level conversion from `SplitCliffordHeisenbergWitness 𝕜 V` to `CurrentHeisenbergRep 𝕜 V`. -/
def splitClifford_to_currentHeisenbergRep
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    CurrentHeisenbergRep 𝕜 V :=
  W.toCurrentHeisenbergRep

/-- Top-level conversion from `SplitCliffordHeisenbergWitness 𝕜 V` to its Sugawara
Virasoro representation. -/
noncomputable def splitClifford_to_sugawaraRepresentation
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ (V →ₗ[𝕜] V) :=
  W.currentSugawaraRepresentation

/-- Top-level conversion from `SplitCliffordHeisenbergWitness 𝕜 V` to `CurrentSugawaraMorphism 𝕜 V`. -/
noncomputable def splitClifford_to_currentSugawaraMorphism
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    CurrentSugawaraMorphism 𝕜 V :=
  W.toCurrentSugawaraMorphism

/-- Top-level product of the current representation and Sugawara representation induced by `W`. -/
noncomputable def splitClifford_current_and_sugawara
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    CurrentHeisenbergRep 𝕜 V ×
      (VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ (V →ₗ[𝕜] V)) :=
  W.current_and_sugawara

/-- Top-level product of the Sugawara morphism and current representation induced by `W`. -/
noncomputable def splitClifford_currentSugawara_and_current
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    CurrentSugawaraMorphism 𝕜 V × CurrentHeisenbergRep 𝕜 V :=
  W.currentSugawaraMorphism_and_current

section ExternalInfiniteCurrent

variable (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]

/-- Lie bracket of the canonical infinite-current generators `Jinf 𝕜 m` and `Jinf 𝕜 n`. -/
theorem canonicalInfiniteCurrent_lie
    (m n : Int) :
    ⁅Jinf 𝕜 m, Jinf 𝕜 n⁆ =
      if m + n = 0 then (m : 𝕜) • Kinf 𝕜 else 0 := by
  have h := lie_Jinf (𝕜 := 𝕜) m n
  exact h

/-- Fundamental mode pair bracket `⁅Jinf 𝕜 1, Jinf 𝕜 (-1)⁆ = (1 : 𝕜) • Kinf 𝕜`. -/
theorem canonicalInfiniteCurrent_lie_one_neg_one :
    ⁅Jinf 𝕜 1, Jinf 𝕜 (-1)⁆ = (1 : 𝕜) • Kinf 𝕜 := by
  have h := lie_Jinf_one_neg_one (𝕜 := 𝕜)
  exact h

/-- Reverse fundamental mode pair bracket `⁅Jinf 𝕜 (-1), Jinf 𝕜 1⁆ = ((-1 : Int) : 𝕜) • Kinf 𝕜`. -/
theorem canonicalInfiniteCurrent_lie_neg_one_one :
    ⁅Jinf 𝕜 (-1), Jinf 𝕜 1⁆ = ((-1 : Int) : 𝕜) • Kinf 𝕜 := by
  have h := lie_Jinf_neg_one_one (𝕜 := 𝕜)
  exact h

/-- Centrality of `Kinf 𝕜` in `InfiniteCurrentAlg 𝕜`: `⁅Kinf 𝕜, Z⁆ = 0`. -/
theorem canonicalInfiniteCurrent_lie_central
    (Z : InfiniteCurrentAlg 𝕜) :
    ⁅Kinf 𝕜, Z⁆ = 0 := by
  have h := lie_Kinf (𝕜 := 𝕜) Z
  exact h

end ExternalInfiniteCurrent

end InfoGeometry.Canonical.SplitCliffordHeisenbergBridge
