import Mathlib.Tactic
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Meta.OwnerTarget
import InfoGeometry.Arithmetic.PrimeExteriorMobiusBridge
import InfoGeometry.Canonical.PrimeBooleanCubeSugawara

/-!
# InfoGeometry.Canonical.PrimeExteriorSugawaraBridge

Finite bridge from the exterior Möbius parity lane to the prime Boolean-cube
Sugawara readout lane.

This file is finite-only. It does not assert any infinite Euler product,
analytic continuation, or Hilbert--Pólya claim.  It simply packages the same
finite prime cutoff into:

* a Möbius/chirality readout on the exterior state;
* a Boolean-cube vertex built from the underlying occupied prime set;
* a Sugawara central-charge readout on that vertex.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeExteriorSugawaraBridge

open InfoGeometry.Arithmetic.PrimeExteriorMobiusBridge
open InfoGeometry.Canonical.PrimeBooleanCubeSugawara
open InfoGeometry.Arithmetic.PrimeBooleanCube

/-- The Boolean-cube vertex naturally attached to a finite exterior state. -/
@[rep_depth thermo]
def vertexOfState {P : PrimeCutoff} (S : SquareFreeState P) : Vertex P where
  val := natSetOfState S
  property := by
    intro n hn
    unfold natSetOfState at hn
    rcases Finset.mem_map.mp hn with ⟨p, _hp, rfl⟩
    exact p.property

/-- The attached Boolean vertex has the same cardinality as the exterior state. -/
@[rep_depth thermo]
theorem vertexOfState_card_eq
    {P : PrimeCutoff}
    (S : SquareFreeState P) :
    (vertexOfState S).val.card = S.card := by
  rw [vertexOfState]
  exact card_natSetOfState S

/-- The finite bridge carrier is already the square-free exterior state.

The former packet added no proof or additional data beyond this field, so the
native carrier is `SquareFreeState P` itself. -/
abbrev PrimeExteriorSugawaraPacket (P : PrimeCutoff) := SquareFreeState P

namespace PrimeExteriorSugawaraPacket

/-- Compatibility readout for the former packet field. -/
abbrev state {P : PrimeCutoff} (B : PrimeExteriorSugawaraPacket P) : SquareFreeState P := B

/-- The Boolean vertex canonically attached to the square-free state. -/
abbrev vertex {P : PrimeCutoff}
    (B : PrimeExteriorSugawaraPacket P) : Vertex P :=
  vertexOfState B.state

@[simp] theorem vertex_eq {P : PrimeCutoff}
    (B : PrimeExteriorSugawaraPacket P) :
    B.vertex = vertexOfState B.state :=
  rfl

variable {P : PrimeCutoff}

/-- The Möbius readout on the exterior state is the global chirality `Γ`. -/
@[bridge_target_tag]
theorem mobius_eq_Gamma (B : PrimeExteriorSugawaraPacket P) :
    ArithmeticFunction.moebius (stateNat B.state) =
      InfoGeometry.Arithmetic.PrimeExteriorRepresentation.SquareFreePrimeState.Gamma B.state := by
  exact InfoGeometry.Arithmetic.PrimeExteriorMobiusBridge.mobius_stateNat_eq_Gamma B.state

/-- The Sugawara readout on the attached Boolean vertex is the state cardinality. -/
@[bridge_target_tag]
theorem centralCharge_eq_card (B : PrimeExteriorSugawaraPacket P) :
    (booleanCubeSugawaraPacket P B.vertex).bridge.centralCharge = B.state.card := by
  rw [B.vertex_eq]
  calc
    (booleanCubeSugawaraPacket P (vertexOfState B.state)).bridge.centralCharge =
        (vertexOfState B.state).val.card :=
      PrimeBooleanCubeSugawaraPacket.centralCharge_eq_card
        (booleanCubeSugawaraPacket P (vertexOfState B.state))
    _ = B.state.card := by
      rw [vertexOfState_card_eq]

end PrimeExteriorSugawaraPacket

/-- Canonical owner target for the finite exterior-to-Sugawara bridge. -/
@[owner_target_tag]
def PrimeExteriorSugawaraOwnerTarget : Prop :=
  ∀ {P : PrimeCutoff} (S : SquareFreeState P),
    ArithmeticFunction.moebius (stateNat S) =
      InfoGeometry.Arithmetic.PrimeExteriorRepresentation.SquareFreePrimeState.Gamma S ∧
    (booleanCubeSugawaraPacket P (vertexOfState S)).bridge.centralCharge = S.card

/-- The finite exterior-to-Sugawara owner target is witnessed by the bridge lemmas. -/
theorem primeExteriorSugawaraOwnerTarget :
    ∀ {P : PrimeCutoff} (S : SquareFreeState P),
      ArithmeticFunction.moebius (stateNat S) =
        InfoGeometry.Arithmetic.PrimeExteriorRepresentation.SquareFreePrimeState.Gamma S ∧
      (booleanCubeSugawaraPacket P (vertexOfState S)).bridge.centralCharge = S.card := by
  intro P S
  constructor
  · exact PrimeExteriorSugawaraPacket.mobius_eq_Gamma
      (S : PrimeExteriorSugawaraPacket P)
  · exact PrimeExteriorSugawaraPacket.centralCharge_eq_card
      (S : PrimeExteriorSugawaraPacket P)

end InfoGeometry.Canonical.PrimeExteriorSugawaraBridge
