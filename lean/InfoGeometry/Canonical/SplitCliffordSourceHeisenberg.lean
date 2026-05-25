import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.Canonical.SplitCliffordHeisenbergBridge
import InfoGeometry.Canonical.SplitCliffordSourceCurrentWick

/-!
# InfoGeometry.Canonical.SplitCliffordSourceHeisenberg

Heisenberg witness packaging from source-side current obligations.

This file is the last source-side step before the existing
`SplitCliffordHeisenbergBridge` and `CurrentSugawaraBridge`.
It is purely structural: it packages proved source obligations; it does not
prove those obligations from split completion data.
-/

namespace InfoGeometry.Canonical.SplitCliffordSourceHeisenberg

open Filter
open InfoGeometry.Canonical.SplitCliffordSourceCarrier
open InfoGeometry.Canonical.SplitCliffordSourceCurrent
open InfoGeometry.Canonical.SplitCliffordSourceCurrentWick
open InfoGeometry.Canonical.SplitCliffordHeisenbergBridge

/--
Owner surface for source-to-endomorphism transport.

This is the exact data still required to close the split-source current debt:
an endomorphism-valued mode family together with truncation and Wick
commutator laws.
-/
structure SplitSourceHeisenbergTransport
    (𝕜 V Carrier : Type*) [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup Carrier] [Module 𝕜 Carrier]
    (S : SplitSourceCarrier 𝕜 V Carrier)
    (Jsrc : SplitSourceCurrent 𝕜 V Carrier S) where
  /-- Transported endomorphism-valued current modes. -/
  Jlift : Int → V →ₗ[𝕜] V
  /-- Local truncation after transport. -/
  truncLift : ∀ v : V, ∀ᶠ l : Int in atTop, Jlift l v = 0
  /-- Wick/Heisenberg commutator after transport. -/
  commLift : SplitSourceEndWickLaw Jlift

/--
Bundle a supplied endomorphism-valued current witness into the split
Heisenberg bridge type.

This function is intentionally strict: it requires the transported mode family
`Jlift` and its truncation/commutator laws as explicit inputs.
-/
def packagedHeisenbergWitness
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (Jlift : Int → V →ₗ[𝕜] V)
    (hTruncLift : ∀ v : V, ∀ᶠ l : Int in atTop, Jlift l v = 0)
    (hCommLift : SplitSourceEndWickLaw Jlift) :
    SplitCliffordHeisenbergWitness 𝕜 V where
  J := Jlift
  trunc := hTruncLift
  comm := hCommLift

/--
Canonical packaging from transport owner data to the split Heisenberg witness.
-/
def transport_to_splitHeisenbergWitness
    {𝕜 V Carrier : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup Carrier] [Module 𝕜 Carrier]
    {S : SplitSourceCarrier 𝕜 V Carrier}
    {Jsrc : SplitSourceCurrent 𝕜 V Carrier S}
    (T : SplitSourceHeisenbergTransport 𝕜 V Carrier S Jsrc) :
    SplitCliffordHeisenbergWitness 𝕜 V :=
  packagedHeisenbergWitness
    (Jlift := T.Jlift)
    (hTruncLift := T.truncLift)
    (hCommLift := T.commLift)

/--
Direct closure from a concrete source transport term to both downstream
representations.
-/
theorem transport_to_current_and_sugawara_nonempty
    {𝕜 V Carrier : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup Carrier] [Module 𝕜 Carrier]
    {S : SplitSourceCarrier 𝕜 V Carrier}
    {Jsrc : SplitSourceCurrent 𝕜 V Carrier S}
    (T : SplitSourceHeisenbergTransport 𝕜 V Carrier S Jsrc) :
    Nonempty (CurrentSugawaraBridge.CurrentHeisenbergRep 𝕜 V) ∧
      Nonempty
        (VirasoroProject.VirasoroAlgebra 𝕜
          →ₗ⁅𝕜⁆ (V →ₗ[𝕜] V)) :=
  (transport_to_splitHeisenbergWitness T).current_and_sugawara_nonempty

/--
Single owner theorem target for source closure:
existence of transported endomorphism-valued current modes with truncation and
Wick commutator law.
-/
def SplitSourceTransportExists
    {𝕜 V Carrier : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup Carrier] [Module 𝕜 Carrier]
    (S : SplitSourceCarrier 𝕜 V Carrier)
    (Jsrc : SplitSourceCurrent 𝕜 V Carrier S) : Prop :=
  Nonempty (SplitSourceHeisenbergTransport 𝕜 V Carrier S Jsrc)

/--
If the source transport target is met, a split Heisenberg witness follows.
-/
theorem splitSourceTransportExists_to_heisenbergWitness
    {𝕜 V Carrier : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup Carrier] [Module 𝕜 Carrier]
    {S : SplitSourceCarrier 𝕜 V Carrier}
    {Jsrc : SplitSourceCurrent 𝕜 V Carrier S}
    (h : SplitSourceTransportExists S Jsrc) :
    Nonempty (SplitCliffordHeisenbergWitness 𝕜 V) := by
  rcases h with ⟨T⟩
  exact ⟨transport_to_splitHeisenbergWitness T⟩

/--
Canonical debt-label alias:
if source-side transport exists, a split Heisenberg witness exists.
-/
theorem splitSource_to_heisenbergWitness
    {𝕜 V Carrier : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup Carrier] [Module 𝕜 Carrier]
    {S : SplitSourceCarrier 𝕜 V Carrier}
    {Jsrc : SplitSourceCurrent 𝕜 V Carrier S}
    (h : SplitSourceTransportExists S Jsrc) :
    Nonempty (SplitCliffordHeisenbergWitness 𝕜 V) :=
  splitSourceTransportExists_to_heisenbergWitness h

/--
Direct closure: source transport existence yields a current Heisenberg
representation through the strict witness packager and existing bridge.
-/
theorem splitSourceTransportExists_to_currentHeisenbergRep
    {𝕜 V Carrier : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup Carrier] [Module 𝕜 Carrier]
    {S : SplitSourceCarrier 𝕜 V Carrier}
    {Jsrc : SplitSourceCurrent 𝕜 V Carrier S}
    (h : SplitSourceTransportExists S Jsrc) :
    Nonempty (CurrentSugawaraBridge.CurrentHeisenbergRep 𝕜 V) := by
  rcases splitSourceTransportExists_to_heisenbergWitness (S := S) (Jsrc := Jsrc) h with ⟨W⟩
  exact W.nonempty_currentHeisenbergRep

/--
Direct bundled closure: source transport existence yields both current and
Sugawara/Virasoro representations.
-/
theorem splitSourceTransportExists_to_current_and_sugawara
    {𝕜 V Carrier : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup Carrier] [Module 𝕜 Carrier]
    {S : SplitSourceCarrier 𝕜 V Carrier}
    {Jsrc : SplitSourceCurrent 𝕜 V Carrier S}
    (h : SplitSourceTransportExists S Jsrc) :
    Nonempty (CurrentSugawaraBridge.CurrentHeisenbergRep 𝕜 V) ∧
      Nonempty
        (VirasoroProject.VirasoroAlgebra 𝕜
          →ₗ⁅𝕜⁆ (V →ₗ[𝕜] V)) := by
  rcases splitSourceTransportExists_to_heisenbergWitness (S := S) (Jsrc := Jsrc) h with ⟨W⟩
  exact W.current_and_sugawara_nonempty

end InfoGeometry.Canonical.SplitCliffordSourceHeisenberg
