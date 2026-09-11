import InfoGeometry.Canonical.Spin44CharacterShadow
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SouriauTheoremTranslatorPacket
import InfoGeometry.Canonical.SplitCl44TKKJordanLieBridge

/-!
# Theory Shadow Representation

This module records the current finite/bridge/owner/debt status of the MIG
shadow corridor in Lean. It deliberately does not promote finite character
sums, Type III/Dixmier regularization, Pfaffian identities, or Witten-index
language to owner theorems.

The role of this file is classification plus theorem-backed projection:

* `Spin44CharacterShadow` remains a finite D4 weight-sum shadow.
* exact KKT residuals are owner-backed constructive data.
* split `Cl(4,4)` / TKK / Jordan-Lie closure is bridge-owned by the recursive
  split-Clifford corridor.
* Dixmier/Drazin partition claims remain explicit debt.
-/

namespace InfoGeometry.Canonical.TheoryShadow

open scoped BigOperators
open scoped InnerProductSpace

open InfoGeometry.Canonical.Spin44CharacterShadow
open InfoGeometry.Canonical.SouriauTheoremTranslatorPacket
open InfoGeometry.Canonical.SouriauLieThermoKKTBridge
open InfoGeometry.Canonical.SouriauFenchelOnsagerBridge
open InfoGeometry.Canonical.SouriauThermodynamics
open InfoGeometry.Canonical.SplitCl44TKKJordanLieBridge

/-- Closure status of a theory lane in the current repository. -/
@[rep_depth thermo]
inductive ShadowStatus where
 | finiteShadow
 | bridgeOwned
 | ownerOwned
 | debt
deriving DecidableEq, Repr

/--
Current shadow representation of the theory corridor.

The equalities are not decorative metadata: they make every advertised status a
kernel-checked field, so downstream users cannot silently treat a debt item as
an owner theorem.
-/
@[rep_depth thermo]
abbrev TheoryShadowStatusVector :=
  ShadowStatus × ShadowStatus × ShadowStatus × ShadowStatus × ShadowStatus

def TheoryShadowRepresentation : Prop :=
  ∃ s : TheoryShadowStatusVector,
    s.1 = ShadowStatus.finiteShadow ∧
    s.2.1 = ShadowStatus.ownerOwned ∧
    s.2.2.1 = ShadowStatus.bridgeOwned ∧
    s.2.2.2.1 = ShadowStatus.debt ∧
    s.2.2.2.2 = ShadowStatus.debt

abbrev CurrentTheoryShadowRepresentation :=
  {s : TheoryShadowStatusVector //
    s.1 = ShadowStatus.finiteShadow ∧
    s.2.1 = ShadowStatus.ownerOwned ∧
    s.2.2.1 = ShadowStatus.bridgeOwned ∧
    s.2.2.2.1 = ShadowStatus.debt ∧
    s.2.2.2.2 = ShadowStatus.debt}

def currentStatus : CurrentTheoryShadowRepresentation :=
  ⟨(ShadowStatus.finiteShadow, ShadowStatus.ownerOwned,
      ShadowStatus.bridgeOwned, ShadowStatus.debt, ShadowStatus.debt), by
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

def CurrentTheoryShadowRepresentation.spin44CharacterStatus
    (C : CurrentTheoryShadowRepresentation) : ShadowStatus := C.1.1

def CurrentTheoryShadowRepresentation.exactKKTResidualStatus
    (C : CurrentTheoryShadowRepresentation) : ShadowStatus := C.1.2.1

def CurrentTheoryShadowRepresentation.splitCl44TKKStatus
    (C : CurrentTheoryShadowRepresentation) : ShadowStatus := C.1.2.2.1

def CurrentTheoryShadowRepresentation.drazinDixmierStatus
    (C : CurrentTheoryShadowRepresentation) : ShadowStatus := C.1.2.2.2.1

def CurrentTheoryShadowRepresentation.pfaffianWittenIndexStatus
    (C : CurrentTheoryShadowRepresentation) : ShadowStatus := C.1.2.2.2.2

theorem CurrentTheoryShadowRepresentation.spin44_is_finiteShadow
    (C : CurrentTheoryShadowRepresentation) :
    C.spin44CharacterStatus = ShadowStatus.finiteShadow := C.2.1

theorem CurrentTheoryShadowRepresentation.exactKKT_is_ownerOwned
    (C : CurrentTheoryShadowRepresentation) :
    C.exactKKTResidualStatus = ShadowStatus.ownerOwned := C.2.2.1

theorem CurrentTheoryShadowRepresentation.splitCl44TKK_is_bridgeOwned
    (C : CurrentTheoryShadowRepresentation) :
    C.splitCl44TKKStatus = ShadowStatus.bridgeOwned := C.2.2.2.1

theorem CurrentTheoryShadowRepresentation.drazinDixmier_is_debt
    (C : CurrentTheoryShadowRepresentation) :
    C.drazinDixmierStatus = ShadowStatus.debt := C.2.2.2.2.1

theorem CurrentTheoryShadowRepresentation.pfaffianWittenIndex_is_debt
    (C : CurrentTheoryShadowRepresentation) :
    C.pfaffianWittenIndexStatus = ShadowStatus.debt := C.2.2.2.2.2

namespace TheoryShadowRepresentation

def spin44CharacterStatus (C : CurrentTheoryShadowRepresentation) : ShadowStatus :=
  C.spin44CharacterStatus

def exactKKTResidualStatus (C : CurrentTheoryShadowRepresentation) : ShadowStatus :=
  C.exactKKTResidualStatus

def splitCl44TKKStatus (C : CurrentTheoryShadowRepresentation) : ShadowStatus :=
  C.splitCl44TKKStatus

def drazinDixmierStatus (C : CurrentTheoryShadowRepresentation) : ShadowStatus :=
  C.drazinDixmierStatus

def pfaffianWittenIndexStatus (C : CurrentTheoryShadowRepresentation) : ShadowStatus :=
  C.pfaffianWittenIndexStatus

theorem spin44_is_finiteShadow (C : CurrentTheoryShadowRepresentation) :
    C.spin44CharacterStatus = ShadowStatus.finiteShadow :=
  C.spin44_is_finiteShadow

theorem exactKKT_is_ownerOwned (C : CurrentTheoryShadowRepresentation) :
    C.exactKKTResidualStatus = ShadowStatus.ownerOwned :=
  C.exactKKT_is_ownerOwned

theorem splitCl44TKK_is_bridgeOwned (C : CurrentTheoryShadowRepresentation) :
    C.splitCl44TKKStatus = ShadowStatus.bridgeOwned :=
  C.splitCl44TKK_is_bridgeOwned

theorem drazinDixmier_is_debt (C : CurrentTheoryShadowRepresentation) :
    C.drazinDixmierStatus = ShadowStatus.debt :=
  C.drazinDixmier_is_debt

theorem pfaffianWittenIndex_is_debt (C : CurrentTheoryShadowRepresentation) :
    C.pfaffianWittenIndexStatus = ShadowStatus.debt :=
  C.pfaffianWittenIndex_is_debt

end TheoryShadowRepresentation

/-- The repository-current shadow classification. -/
@[rep_depth thermo]
def current : CurrentTheoryShadowRepresentation := currentStatus

@[rep_depth thermo]
theorem current_spin44_is_finiteShadow :
 current.spin44CharacterStatus = ShadowStatus.finiteShadow :=
 current.spin44_is_finiteShadow

@[rep_depth thermo]
theorem current_exactKKT_is_ownerOwned :
 current.exactKKTResidualStatus = ShadowStatus.ownerOwned :=
 current.exactKKT_is_ownerOwned

@[rep_depth thermo]
theorem current_splitCl44TKK_is_bridgeOwned :
 current.splitCl44TKKStatus = ShadowStatus.bridgeOwned :=
 current.splitCl44TKK_is_bridgeOwned

@[rep_depth thermo]
theorem current_noDixmierOwner :
 current.drazinDixmierStatus = ShadowStatus.debt :=
 current.drazinDixmier_is_debt

@[rep_depth thermo]
theorem current_noPfaffianWittenIndexOwner :
 current.pfaffianWittenIndexStatus = ShadowStatus.debt :=
 current.pfaffianWittenIndex_is_debt

/-! ## Theorem-backed shadow projections -/

/--
The `Spin(4,4)` character lane currently owns only the finite D4 vector
character shadow.
-/
@[rep_depth thermo]
theorem spin44_vectorCharacter_shadow_eq_two_sum_cosh
 (β : Cartan4) :
 vectorCharacter β = vectorCharacterCosh β :=
 vectorCharacter_eq_two_sum_cosh β

/-!
Dimension-agnostic KKT owner lane.

This packet is independent of any finite index carrier and is the primary
constructive owner for the exact residual branch.
-/
@[rep_depth thermo]
theorem exactKKT_dimensionAgnostic_stationarity_packet :
 let K := DimensionAgnosticKKTResiduals.exact.toShadow
 K.coneAdmissible ∧ K.stationarity ∧
 K.complementarySlackness ∧ K.finitePartitionAdmissible :=
 DimensionAgnosticKKTResiduals.exact_stationarity_packet

/-- Backward-compatible alias to the dimension-agnostic owner packet. -/
@[rep_depth thermo]
theorem exactKKT_owner_constructs_stationarity_packet :
 let K := DimensionAgnosticKKTResiduals.exact.toShadow
 K.coneAdmissible ∧ K.stationarity ∧
 K.complementarySlackness ∧ K.finitePartitionAdmissible :=
 exactKKT_dimensionAgnostic_stationarity_packet

/--
Finite translator corollary.

The dimension-agnostic exact-residual owner packet is imported unchanged, while
the finite Souriau/Fisher side still requires its PSD witness.
-/
@[rep_depth thermo]
theorem exactKKT_translator_shadow_packet
 [Fintype α] [Nonempty α]
 (C : SouriauFenchelContext (α := α))
 (hPSD : (souriauFisherResponseMatrix C.M C.T).PositiveSemidefinite)
 (eta xβ xμ : ℝ) :
 (DimensionAgnosticKKTResiduals.exact.toShadow).coneAdmissible
 ∧ (DimensionAgnosticKKTResiduals.exact.toShadow).stationarity
 ∧ (DimensionAgnosticKKTResiduals.exact.toShadow).complementarySlackness
 ∧ (DimensionAgnosticKKTResiduals.exact.toShadow).finitePartitionAdmissible := by
 have out := structuredSouriauKKTTranslatorPacket_ofExactWitness
   (C := C) hPSD eta xβ xμ
 exact out.2

/--
The split `Cl(4,4)` / TKK lane is bridge-owned by the recursive split-Clifford
packet and the doubled triality proxy, not by a full `Spin(4,4)` classification.
-/
@[rep_depth transport]
theorem splitCl44_TKK_shadow_bridge_packet
 [Fintype α] [Nonempty α]
 {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
 (P : SplitCl44TKKJordanLiePacket (α := α) (H := H))
 (x : ℝ × ℝ) (xs : InfoGeometry.Canonical.SplitCliffordTensorBridge.SplitClNNCarrier 3) :
 P.closure.gibbs.SatisfiesOperatorTKKMasterRelation P.closure.tkkParameter
 ∧ P.closure.gibbs.IsOperatorAdmissible
 ∧ P.triality.informationalDiracSquare = LinearMap.id := by
 have h := P.splitCl44_TKK_JordanLie_constructive_packet x xs
 exact ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.1⟩

end InfoGeometry.Canonical.TheoryShadow
