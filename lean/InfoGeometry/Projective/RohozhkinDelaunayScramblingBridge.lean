import InfoGeometry.Topology.RohozhkinRepresentation
import InfoGeometry.Topology.RohozhkinPentagonMatrix
import InfoGeometry.Projective.HorizonInformationScrambling

/-!
# Rohozhkin/Delaunay Horizon Braiding Bridge

This file connects the repo-owned Rohozhkin/Delaunay pure-braid boundary to the
finite horizon-braiding interface.

It deliberately proves only readback/interface facts:

* the Rohozhkin source shape has `moving + 3` points and `2 * moving + 1`
  internal triangle coordinates, matching the paper convention after the outer
  triangle is removed;
* a completed `RohozhkinDelaunayBraidingSpec` descends to the presented pure
  braid group by the existing topology owner;
* if a pure braid is separately assigned a `ModularTimeFlow`, the existing
  finite horizon packet gives unitarity and information conservation readbacks;
* if a Fibonacci phase/readout is separately supplied, the existing Fibonacci
  owner gives adjacent braid-rewrite invariance.

No theorem here constructs Rohozhkin's nontrivial generator matrices, proves
they are unitary, identifies them with Majorana/Fibonacci anyons, proves
Yang--Baxter, establishes Markov invariance, or derives a scrambling estimate.
-/

namespace RohozhkinDelaunayScramblingBridge

open InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding
open InfoGeometry.Projective.Scrambling
open InfoGeometry.Topology.Delaunay
open InfoGeometry.Topology.PureBraid
open InfoGeometry.Topology.RohozhkinBoundary

abbrev RohozhkinDelaunayBraidingSpec :=
  InfoGeometry.Topology.RohozhkinRepresentation.RohozhkinDelaunayBraidingSpec

/-! ## Source-shape readbacks -/

/-- Rohozhkin's internal triangle-basis dimension in the repo convention. -/
abbrev rohozhkinTriangleBasisDim (moving : ℕ) : ℕ :=
  rohozhkinDim moving

/-- The paper convention after deleting the outer triangle gives `2 * moving + 1`. -/
theorem rohozhkinTriangleBasisDim_eq_two_mul_add_one (moving : ℕ) :
    rohozhkinTriangleBasisDim moving = 2 * moving + 1 := by
  rfl

/-- Rohozhkin's source uses `moving` interior points plus three fixed boundary points. -/
theorem rohozhkinTotalPointCount_eq_moving_add_three (moving : ℕ) :
    rohozhkinTotalPoints moving = moving + 3 := by
  rfl

/-! ## Pure-braid descent readback -/

/--
Projective-side packet for a completed Rohozhkin/Delaunay representation.

The field `delaunay` is the only source of a pure-braid representation.  It is
already assumption-indexed by a concrete generator assignment and a proof that
all presented pure-braid relators evaluate to `1`.
-/
structure RohozhkinProjectiveBraidPacket (moving : ℕ) where
  delaunay : RohozhkinDelaunayBraidingSpec moving

/-- The descended pure-braid matrix representation supplied by the topology owner. -/
noncomputable def RohozhkinProjectiveBraidPacket.representation {moving : ℕ}
    (P : RohozhkinProjectiveBraidPacket moving) :
    RohozhkinPureBraidGroup moving →* RohozhkinMatrixUnits moving :=
  P.delaunay.representation

/-- Generator readout for the descended Rohozhkin representation. -/
@[simp]
theorem RohozhkinProjectiveBraidPacket.representation_of {moving : ℕ}
    (P : RohozhkinProjectiveBraidPacket moving)
    (g : PureBraidGenerator (rohozhkinTotalPoints moving)) :
    P.representation (of g) = P.delaunay.gen g := by
  change P.delaunay.representation (of g) = P.delaunay.gen g
  exact P.delaunay.representation_of g

/-- Existence packet for the descended representation. -/
theorem rohozhkin_projective_braid_descent_packet {moving : ℕ}
    (P : RohozhkinProjectiveBraidPacket moving) :
    ∃ ρ : RohozhkinPureBraidGroup moving →* RohozhkinMatrixUnits moving,
      ∀ g : PureBraidGenerator (rohozhkinTotalPoints moving), ρ (of g) = P.delaunay.gen g :=
  P.delaunay.descent_packet

/-! ## Horizon-flow interface -/

/--
Assumption-indexed realization of Rohozhkin pure braids as finite horizon flows.

`flowOf` is explicit data.  This file does not derive it from the rational
Delaunay matrices, because those matrices are not yet proved to be a unitary
Majorana/Fibonacci representation.
-/
structure RohozhkinHorizonFlowRealization (moving horizonDim : ℕ) where
  packet : RohozhkinProjectiveBraidPacket moving
  flowOf : RohozhkinPureBraidGroup moving → ModularTimeFlow horizonDim

/-- The finite flow attached to a pure braid by a supplied realization. -/
def RohozhkinHorizonFlowRealization.flow {moving horizonDim : ℕ}
    (R : RohozhkinHorizonFlowRealization moving horizonDim)
    (β : RohozhkinPureBraidGroup moving) : ModularTimeFlow horizonDim :=
  R.flowOf β

/--
If a Rohozhkin pure braid has been supplied as a `ModularTimeFlow`, the existing
finite horizon packet gives unitarity plus information conservation.
-/
theorem rohozhkin_horizon_flow_packet {moving horizonDim : ℕ}
    (R : RohozhkinHorizonFlowRealization moving horizonDim)
    (β : RohozhkinPureBraidGroup moving)
    (state : HorizonMicrostates horizonDim) :
    IsUnitaryBraiding (R.flow β) ∧ InformationIsConserved (R.flow β) state :=
  finite_unitary_braiding_packet (R.flow β) state

/-! ## Fibonacci phase readout interface -/

/--
Assumption-indexed Fibonacci/MZM readout for the Rohozhkin boundary.

The `phase` and `readout` fields are supplied data.  They are not derived from
Rohozhkin matrices here.
-/
structure RohozhkinFibonacciReadout (moving : ℕ) (Gate : Type*) [SMul (Units ℂ) Gate] where
  packet : RohozhkinProjectiveBraidPacket moving
  phase : FibonacciBraidPhase
  readout : Equiv.Perm ℕ → Gate
  braidPhase_rewrite :
    ∀ (i : ℕ) (left right : FibonacciBraidWord),
      phase (left ++ [i, i + 1, i] ++ right) =
        phase (left ++ [i + 1, i, i + 1] ++ right)

/--
A supplied Rohozhkin/Fibonacci phase readout is invariant under the adjacent
braid rewrite, by the finite Fibonacci owner.
-/
theorem rohozhkin_fibonacci_projective_gate_braid_rewrite
    {moving : ℕ} (Gate : Type*) [SMul (Units ℂ) Gate]
    (R : RohozhkinFibonacciReadout moving Gate)
    (i : ℕ) (left right : FibonacciBraidWord) :
    fibonacciProjectiveGate Gate R.phase R.readout
        (left ++ [i, i + 1, i] ++ right) =
      fibonacciProjectiveGate Gate R.phase R.readout
        (left ++ [i + 1, i, i + 1] ++ right) := by
  exact fibonacciProjectiveGate_braid_rewrite_of_phase Gate R.phase R.readout
    i left right (R.braidPhase_rewrite i left right)

end RohozhkinDelaunayScramblingBridge
