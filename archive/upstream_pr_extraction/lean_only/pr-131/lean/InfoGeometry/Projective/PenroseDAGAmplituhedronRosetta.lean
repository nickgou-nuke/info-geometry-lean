import InfoGeometry.Canonical.ProofCausalityBridge
import InfoGeometry.Geometry.PenroseKleinTiling
import InfoGeometry.Projective.SplitQuaternionMatrix
import InfoGeometry.Projective.TwistorAmplituhedronConfigurationBridge
import InfoGeometry.Topology.DelaunayAdjacentStructures

/-!
# Penrose / DAG / Amplituhedron Rosetta Data

This file records the theorem-safe form of the slogan that the DAG graph, split
quaternion matrix model, Penrose net, Klein quadric lane, amplituhedron lane,
and Delaunay tessellation lane are "the same".

The kernel-checked content is deliberately narrower:

* a `RosettaData` record identifies each lane with a common
  carrier type;
* all transport between lanes is by the supplied equivalences;
* existing owner files provide finite readbacks for the DAG, split quaternion,
  Penrose/Klein, Klein/twistor, amplituhedron-interface, and Delaunay lanes.

No theorem here constructs the geometric equivalences between these lanes.
Those comparisons remain owner theorems/debt, represented here by explicit
carrier equivalences.
-/

namespace InfoGeometry.Projective.PenroseDAGAmplituhedronRosetta

open InfoGeometry.Projective.TwistorAmplituhedronConfigurationBridge
open InfoGeometry.Projective.TwistorAmplituhedronConfigurationBridge.Plucker6

/-- The six lanes participating in the Rosetta dictionary. -/
inductive RosettaLane where
  | dagGraph
  | splitQuaternion
  | penroseNet
  | kleinQuadric
  | amplituhedron
  | delaunayTessellation
  deriving DecidableEq, Repr

/--
Explicit common-carrier datum.

For each lane, `Carrier lane` is that lane's local model, and `toCommon lane`
is the supplied equivalence into the chosen common carrier.
-/
structure RosettaData where
  Carrier : RosettaLane → Type u
  Common : Type v
  toCommon : ∀ lane : RosettaLane, Carrier lane ≃ Common

namespace RosettaData

/-- Transport between any two lanes through the supplied common carrier. -/
def laneEquiv (R : RosettaData) (a b : RosettaLane) :
    R.Carrier a ≃ R.Carrier b :=
  (R.toCommon a).trans (R.toCommon b).symm

/-- Two lane elements are the same Rosetta datum when their common images agree. -/
def SameInCommon (R : RosettaData) {a b : RosettaLane}
    (x : R.Carrier a) (y : R.Carrier b) : Prop :=
  R.toCommon a x = R.toCommon b y

@[simp]
theorem toCommon_laneEquiv (R : RosettaData) (a b : RosettaLane)
    (x : R.Carrier a) :
    R.toCommon b (R.laneEquiv a b x) = R.toCommon a x := by
  simp [laneEquiv]

@[simp]
theorem laneEquiv_sameInCommon (R : RosettaData) (a b : RosettaLane)
    (x : R.Carrier a) :
    R.SameInCommon x (R.laneEquiv a b x) := by
  simp [SameInCommon]

theorem sameInCommon_iff_laneEquiv_eq (R : RosettaData)
    {a b : RosettaLane} (x : R.Carrier a) (y : R.Carrier b) :
    R.SameInCommon x y ↔ R.laneEquiv a b x = y := by
  constructor
  · intro h
    apply (R.toCommon b).injective
    change
      R.toCommon b ((R.toCommon b).symm (R.toCommon a x)) =
        R.toCommon b y
    simpa [SameInCommon] using h
  · intro h
    rw [← h]
    simp [SameInCommon]

/-- Predicates on the common carrier transport to every lane. -/
theorem transport_common_predicate (R : RosettaData)
    (P : R.Common → Prop) {a b : RosettaLane}
    (x : R.Carrier a) (h : P (R.toCommon a x)) :
    P (R.toCommon b (R.laneEquiv a b x)) := by
  simpa using h

end RosettaData

/-! ## Owner readbacks for the six lanes -/

/-- DAG lane readback: the existing declaration-DAG Hodge bridge target. -/
theorem dag_graph_hodge_readback
    {α : Type*} [BEq α] [Hashable α] :
    DAG.GraphHodgeBridgeTarget α :=
  InfoGeometry.Canonical.ProofCausalityBridge.graphHodgeBridgeTarget

/-- Split-quaternion lane readback: the concrete algebra equivalence with `M₂(ℝ)`. -/
theorem split_quaternion_matrix_equiv_readback :
    Nonempty
      (InfoGeometry.Projective.SplitQuaternion ≃ₐ[ℝ]
        Matrix (Fin 2) (Fin 2) ℝ) :=
  ⟨InfoGeometry.Projective.splitQuaternionMatrixEquiv⟩

/-- Split-quaternion norm readback: determinant equals the split quadratic norm. -/
theorem split_quaternion_det_norm_readback
    (q : InfoGeometry.Projective.SplitQuaternion) :
    (InfoGeometry.Projective.splitQuaternionToMatrixQ q).det =
      InfoGeometry.Projective.splitNormSq q.w q.x q.y q.z :=
  InfoGeometry.Projective.det_eq_splitNormSq q.w q.x q.y q.z

/-- Penrose-net lane readback: one Klein-bottle glide step of the Penrose basis sheet. -/
theorem penrose_klein_glide_readback (x y : ℝ) :
    InfoGeometry.Geometry.PenroseKlein.KleinBottleRel (x, y) (-x, y + 1) :=
  InfoGeometry.Geometry.PenroseKlein.penrose_klein_defect_localization x y

/-- Klein-quadric lane readback from the twistor/amplituhedron configuration owner. -/
theorem klein_quadric_line_readback {moving : ℕ}
    (D : TwistorAmplituhedronBridgeDatum moving) (i : Fin 3) :
    InfoGeometry.Projective.KleinQuadric.Plucker6.IsKlein (D.lines.line i) :=
  D.lines.line_isKlein i

/-- Amplituhedron-interface lane readback: the supplied rank budget matches the spin tiling. -/
theorem amplituhedron_rank_budget_readback {moving : ℕ}
    (D : TwistorAmplituhedronBridgeDatum moving) :
    D.rank.data.totalRank *
      InfoGeometry.Projective.PenroseSpinTiling.spinTilingMultiplicity =
        D.rank.stateBudget :=
  spin_tiled_rank_matches_stateBudget D.rank

/-- Delaunay lane readback: a completed Rohozhkin packet descends to a pure-braid representation. -/
theorem delaunay_pure_braid_descent_readback {moving : ℕ}
    (D : TwistorAmplituhedronBridgeDatum moving) :
    ∃ ρ :
      InfoGeometry.Topology.RohozhkinBoundary.RohozhkinPureBraidGroup moving →*
        InfoGeometry.Topology.RohozhkinBoundary.RohozhkinMatrixUnits moving,
      ∀ g :
        InfoGeometry.Topology.PureBraid.PureBraidGenerator
          (InfoGeometry.Topology.Delaunay.rohozhkinTotalPoints moving),
        ρ (InfoGeometry.Topology.PureBraid.of g) = InfoGeometry.Projective.RohozhkinDelaunayScramblingBridge.rohozhkinProjectiveBraidPacketGen D.rohozhkin.packet g :=
  rohozhkin_plabic_descent_packet D.rohozhkin

/--
Compact packet: the carrier supplies the cross-lane identification; the owner
files supply the currently closed readbacks.
-/
theorem rosetta_dag_amplituhedron_equiv (R : RosettaData) :
    Nonempty (R.Carrier RosettaLane.dagGraph ≃
      R.Carrier RosettaLane.amplituhedron) :=
  ⟨R.laneEquiv RosettaLane.dagGraph RosettaLane.amplituhedron⟩

theorem rosetta_penrose_origin_glide :
    InfoGeometry.Geometry.PenroseKlein.KleinBottleRel
      ((0 : ℝ), (0 : ℝ)) (0, 1) := by
  simpa using penrose_klein_glide_readback (0 : ℝ) (0 : ℝ)

end InfoGeometry.Projective.PenroseDAGAmplituhedronRosetta
