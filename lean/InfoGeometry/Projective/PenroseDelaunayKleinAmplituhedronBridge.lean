import InfoGeometry.Algebra.SplitQuaternionMatrices
import InfoGeometry.Canonical.ProofDAGRepresentationBridge
import InfoGeometry.Geometry.PenroseKleinTiling
import InfoGeometry.Projective.TwistorAmplituhedronConfigurationBridge

/-!
# Penrose / Delaunay / Klein / Amplituhedron Comparison Corridor

This file records the theorem-safe meaning of the slogan that the repository's
proof DAG, split-quaternion model, Penrose net, Delaunay tessellation, Klein
quadric, and amplituhedron boundary are "the same".

Closed here:

* the split-quaternion matrix owner gives the `(2,2)` Klein determinant readout;
* the Penrose/Klein tiling owner gives the one-step Klein glide readout;
* a supplied family of equivalences composes to a DAG-to-amplituhedron carrier;
* if the supplied equivalences commute, the Klein and Delaunay routes agree;
* the existing twistor/amplituhedron packet still supplies the Klein-line,
  rank-budget, and Rohozhkin pure-braid descent readouts.

Not closed here:

* no theorem proves that these carriers are definitionally equal;
* no theorem constructs the amplituhedron or its positive geometry;
* no theorem identifies Delaunay flips with plabic square moves;
* no theorem derives the comparison equivalences from the proof DAG itself.
-/

namespace InfoGeometry.Projective.PenroseDelaunayKleinAmplituhedronBridge

open InfoGeometry.Projective.TwistorAmplituhedronConfigurationBridge
open InfoGeometry.Projective.PenroseSpinTiling
open InfoGeometry.Topology.Delaunay
open InfoGeometry.Topology.PureBraid
open InfoGeometry.Topology.RohozhkinBoundary

/-! ## Owner readouts -/

/-- The proof-DAG owner supplies antisymmetry/no-loop for represented causal edges. -/
theorem proof_dag_no_loop_readout {α : Type*}
    (G : InfoGeometry.Canonical.ProofDAGRepresentationBridge.ProofDAG α)
    (R : InfoGeometry.Canonical.ProofDAGRepresentationBridge.CausalRepresentation G)
    {a b : α}
    (hab : G.le a b)
    (hba : G.le b a) :
    a = b :=
  InfoGeometry.Canonical.ProofDAGRepresentationBridge.represented_no_loop
    G R hab hba

/-- The split-quaternion matrix owner realizes the Klein `(2,2)` quadratic form. -/
theorem split_quaternion_klein_norm_readout (w x y z : ℝ) :
    InfoGeometry.Algebra.SplitQuaternionMatrices.det2
        (InfoGeometry.Algebra.SplitQuaternionMatrices.splitQ w x y z) =
      w * w + x * x - y * y - z * z :=
  InfoGeometry.Algebra.SplitQuaternionMatrices.det2_splitQ w x y z

/-- The Penrose/Klein tiling owner supplies the local non-orientable glide. -/
theorem penrose_klein_glide_readout (x y : ℝ) :
    InfoGeometry.Geometry.PenroseKlein.KleinBottleRel (x, y) (-x, y + 1) :=
  InfoGeometry.Geometry.PenroseKlein.penrose_klein_defect_localization x y

/-! ## Abstract comparison corridor -/

universe u

/--
Explicit carrier data for the comparison corridor.

Every arrow is a supplied equivalence.  This structure deliberately avoids
asserting that a proof DAG, a Penrose net, a Delaunay tessellation, a Klein
quadric model, and an amplituhedron boundary are literally the same type.
-/
structure PenroseDelaunayKleinAmplituhedronCorridor (moving : ℕ) where
  DagCarrier : Type u
  SplitQuaternionCarrier : Type u
  PenroseNetCarrier : Type u
  DelaunayCarrier : Type u
  KleinQuadricCarrier : Type u
  AmplituhedronCarrier : Type u
  dagToPenrose : DagCarrier ≃ PenroseNetCarrier
  penroseToDelaunay : PenroseNetCarrier ≃ DelaunayCarrier
  penroseToKlein : PenroseNetCarrier ≃ KleinQuadricCarrier
  splitQuaternionToKlein : SplitQuaternionCarrier ≃ KleinQuadricCarrier
  delaunayToAmplituhedron : DelaunayCarrier ≃ AmplituhedronCarrier
  kleinToAmplituhedron : KleinQuadricCarrier ≃ AmplituhedronCarrier
  twistor : TwistorAmplituhedronBridgeDatum moving

namespace PenroseDelaunayKleinAmplituhedronCorridor

variable {moving : ℕ}

/-- DAG-to-amplituhedron route through Penrose and Klein data. -/
def dagToAmplituhedronViaKlein
    (C : PenroseDelaunayKleinAmplituhedronCorridor.{u} moving) :
    C.DagCarrier ≃ C.AmplituhedronCarrier :=
  (C.dagToPenrose.trans C.penroseToKlein).trans C.kleinToAmplituhedron

/-- DAG-to-amplituhedron route through Penrose and Delaunay data. -/
def dagToAmplituhedronViaDelaunay
    (C : PenroseDelaunayKleinAmplituhedronCorridor.{u} moving) :
    C.DagCarrier ≃ C.AmplituhedronCarrier :=
  (C.dagToPenrose.trans C.penroseToDelaunay).trans C.delaunayToAmplituhedron

/-- Split-quaternion-to-amplituhedron route through the Klein carrier. -/
def splitQuaternionToAmplituhedronViaKlein
    (C : PenroseDelaunayKleinAmplituhedronCorridor.{u} moving) :
    C.SplitQuaternionCarrier ≃ C.AmplituhedronCarrier :=
  C.splitQuaternionToKlein.trans C.kleinToAmplituhedron

/--
The precise commuting-diagram condition for the slogan "the Penrose/Delaunay
and Penrose/Klein readings are the same".
-/
def RoutesCommute
    (C : PenroseDelaunayKleinAmplituhedronCorridor.{u} moving) : Prop :=
  C.dagToAmplituhedronViaKlein = C.dagToAmplituhedronViaDelaunay

/-- Read back a supplied commuting-diagram proof. -/
theorem routes_commute_readout
    (C : PenroseDelaunayKleinAmplituhedronCorridor.{u} moving)
    (h : C.RoutesCommute) :
    C.RoutesCommute :=
  h

/--
The combined corridor packet.

If the comparison routes commute, then the DAG, split-quaternion, Penrose,
Delaunay, Klein, and amplituhedron carriers can be used through the same
amplituhedron carrier, while the existing twistor/amplituhedron owner still
supplies its finite Klein-line, rank, and Rohozhkin descent readouts.
-/
theorem comparison_corridor_packet
    (C : PenroseDelaunayKleinAmplituhedronCorridor.{u} moving)
    (i : Fin 3)
    (hComm : C.RoutesCommute) :
    Nonempty (C.DagCarrier ≃ C.AmplituhedronCarrier) ∧
      Nonempty (C.SplitQuaternionCarrier ≃ C.AmplituhedronCarrier) ∧
      C.RoutesCommute ∧
      InfoGeometry.Projective.KleinQuadric.Plucker6.IsKlein
        (C.twistor.lines.line i) ∧
      C.twistor.rank.data.totalRank * spinTilingMultiplicity =
        C.twistor.rank.stateBudget ∧
      ∃ ρ : RohozhkinPureBraidGroup moving →* RohozhkinMatrixUnits moving,
        ∀ g : PureBraidGenerator (rohozhkinTotalPoints moving),
          ρ (of g) = InfoGeometry.Projective.RohozhkinDelaunayScramblingBridge.rohozhkinProjectiveBraidPacketGen C.twistor.rohozhkin.packet g := by
  have hTwistor := twistor_amplituhedron_bridge_packet C.twistor i
  exact ⟨⟨C.dagToAmplituhedronViaKlein⟩,
    ⟨C.splitQuaternionToAmplituhedronViaKlein⟩,
    hComm,
    hTwistor.1,
    hTwistor.2.1,
    hTwistor.2.2⟩

end PenroseDelaunayKleinAmplituhedronCorridor

end InfoGeometry.Projective.PenroseDelaunayKleinAmplituhedronBridge
