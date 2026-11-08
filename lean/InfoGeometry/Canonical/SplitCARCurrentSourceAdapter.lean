/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CurrentSugawaraBridge

/-!
# Source-Faithful CAR-to-Current Adapter and Sugawara Readout

This module defines the subtype `AdapterData 𝕜 A V` binding a raw CAR mode
completion `RawCARModeCompletion A`, an algebra representation
`ρ : A →+* Module.End 𝕜 V`, represented cutoff currents, and a stabilized
Heisenberg current representation `CurrentHeisenbergRep 𝕜 V`, and derives its
Sugawara Virasoro representation and mode commutator readout.

- BUCKET 1 (Real Math in This File):
  - `AdapterData`
  - `AdapterData.source`, `AdapterData.ρ`, `AdapterData.cutoffCurrent`,
    `AdapterData.toCurrentHeisenbergRep`, `AdapterData.J`,
    `AdapterData.eventually_cutoffCurrent_eq`,
    `AdapterData.cutoffCurrent_eq_represented_rawCurrent`,
    `AdapterData.trunc`, `AdapterData.comm`
  - `AdapterData.toSugawaraVirasoroRepresentation`, `AdapterData.virasoro_bracket_readout`

- BUCKET 2 (Meaningful Mathematical Results Used):
  - `InfoGeometry.Canonical.BosonizationConstructiveCurrent`
  - `InfoGeometry.Canonical.CurrentSugawaraBridge`

- BUCKET 3 (Excluded Wrapper Patterns):
  - Zero wrapper structures, zero `Prop`-valued aliases, and zero `:= rfl` theorems.
-/

namespace InfoGeometry.Canonical.SplitCARCurrentSourceAdapter

attribute [local instance 100] LieRing.ofAssociativeRing

open Filter
open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Canonical.CurrentSugawaraBridge
open VirasoroProject

/-- Subtype of source-faithful CAR-to-current adapter tuples
`(source, ρ, cutoffCurrent, H)` whose cutoff currents equal the represented raw
CAR cutoff currents and stabilize pointwise to `H.J`. -/
def AdapterData (𝕜 A V : Type*) [Field 𝕜] [CharZero 𝕜]
    [Ring A] [AddCommGroup V] [Module 𝕜 V] : Type _ :=
  { D : RawCARModeCompletion A × (A →+* Module.End 𝕜 V) ×
        (ℕ → Int → Module.End 𝕜 V) × CurrentHeisenbergRep 𝕜 V //
      (∀ (m : Int) (v : V), ∀ᶠ L : ℕ in atTop, D.2.2.1 L m v = D.2.2.2.J m v) ∧
      (∀ (L : ℕ) (m : Int), D.2.2.1 L m = D.2.1 (representedCutoffCurrent D.1 L m)) }

namespace AdapterData

variable {𝕜 A V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [Ring A] [AddCommGroup V] [Module 𝕜 V]

/-- Raw CAR mode completion carried by `S`. -/
def source (S : AdapterData 𝕜 A V) : RawCARModeCompletion A :=
  S.val.1

/-- Ring homomorphism representation `A →+* Module.End 𝕜 V` carried by `S`. -/
def ρ (S : AdapterData 𝕜 A V) : A →+* Module.End 𝕜 V :=
  S.val.2.1

/-- Truncated normal-ordered current endomorphisms carried by `S`. -/
def cutoffCurrent (S : AdapterData 𝕜 A V) : ℕ → Int → Module.End 𝕜 V :=
  S.val.2.2.1

/-- Underlying `CurrentHeisenbergRep 𝕜 V` carried by `S`. -/
def toCurrentHeisenbergRep (S : AdapterData 𝕜 A V) : CurrentHeisenbergRep 𝕜 V :=
  S.val.2.2.2

/-- Stabilized limit current modes on `V`. -/
def J (S : AdapterData 𝕜 A V) : Int → Module.End 𝕜 V :=
  S.toCurrentHeisenbergRep.J

/-- Pointwise eventual stabilization of the finite cutoff current action to `S.J m v`. -/
theorem eventually_cutoffCurrent_eq (S : AdapterData 𝕜 A V)
    (m : Int) (v : V) :
    ∀ᶠ L : ℕ in atTop, S.cutoffCurrent L m v = S.J m v := by
  unfold cutoffCurrent J toCurrentHeisenbergRep
  exact S.property.1 m v

/-- Identification of the cutoff current with the represented raw CAR current. -/
theorem cutoffCurrent_eq_represented_rawCurrent (S : AdapterData 𝕜 A V)
    (L : ℕ) (m : Int) :
    S.cutoffCurrent L m = S.ρ (representedCutoffCurrent S.source L m) := by
  unfold cutoffCurrent ρ source
  exact S.property.2 L m

/-- Eventual positive-mode truncation for the limit current family `S.J`. -/
theorem trunc (S : AdapterData 𝕜 A V) :
    ∀ v, ∀ᶠ l : Int in atTop, S.J l v = 0 := by
  intro v
  exact S.toCurrentHeisenbergRep.trunc v

/-- Heisenberg mode commutator law for `S.J`. -/
theorem comm (S : AdapterData 𝕜 A V) :
    ∀ m n, (S.J m).commutator (S.J n) =
      if m + n = 0 then (m : 𝕜) • (1 : Module.End 𝕜 V) else 0 := by
  intro m n
  exact S.toCurrentHeisenbergRep.comm m n

/-- Sugawara Virasoro Lie algebra representation induced by `S`. -/
noncomputable def toSugawaraVirasoroRepresentation
    (S : AdapterData 𝕜 A V) :
    VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ Module.End 𝕜 V :=
  S.toCurrentHeisenbergRep.currentSugawaraRepresentation

/-- Virasoro mode commutator identity for the Sugawara stress-tensor modes of `S`. -/
theorem virasoro_bracket_readout
    (S : AdapterData 𝕜 A V) (m n : Int) :
    (S.toCurrentHeisenbergRep.sugawaraStressMode m).commutator
        (S.toCurrentHeisenbergRep.sugawaraStressMode n) =
      (m - n) • S.toCurrentHeisenbergRep.sugawaraStressMode (m + n) +
        if m + n = 0 then (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) • (1 : Module.End 𝕜 V)) else 0 := by
  have h := S.toCurrentHeisenbergRep.sugawaraStressMode_virasoroBracket m n
  exact h

end AdapterData

end InfoGeometry.Canonical.SplitCARCurrentSourceAdapter
