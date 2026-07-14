import InfoGeometry.Projective.KleinQuadricIncidence
import InfoGeometry.Projective.NonIsoConf3RankIngestion
import InfoGeometry.Projective.RohozhkinDelaunayScramblingBridge
import InfoGeometry.Projective.Twistor.Incidence
import InfoGeometry.Projective.KuzminCuntzPath

/-!
# Twistor / Amplituhedron Configuration Bridge

This module records the theorem-safe part of the split-twistor/amplituhedron
dictionary.

Closed here:

* a three-line Klein/Plücker configuration with pairwise non-incidence;
* readbacks from the existing Penrose twistor and Klein incidence owners;
* a rank-32 budget only from explicit external Betti data plus the existing
  spin-tiling multiplicity;
* Rohozhkin pure-braid descent only from a completed `RohozhkinDelaunayBraidingSpec`;
* BCFW/amplituhedron/plabic claims only as explicit interfaces.

Not closed here:

* no theorem identifies `Conf₃` de Rham cohomology with an amplituhedron volume;
* no theorem identifies Arnold relations with BCFW recursion;
* no theorem identifies Rohozhkin Delaunay flips with plabic square moves;
* no theorem identifies the configured rank `32` with an `N=4` SYM multiplet.
-/

namespace InfoGeometry.Projective.TwistorAmplituhedronConfigurationBridge

open InfoGeometry.Projective.KleinQuadric
open InfoGeometry.Projective.KleinQuadricIncidence
open InfoGeometry.Projective.NonIsoConf3RankIngestion
open InfoGeometry.Projective.PenroseSpinTiling
open InfoGeometry.Projective.RohozhkinDelaunayScramblingBridge
open InfoGeometry.Projective.Twistor
open InfoGeometry.Topology.Delaunay
open InfoGeometry.Topology.PureBraid
open InfoGeometry.Topology.RohozhkinBoundary
open InfoGeometry.Projective.KuzminCuntzPath

namespace Plucker6

/-- Three Plücker/Klein lines with pairwise non-incidence. -/
structure KleinLineConfig3 where
  line : Fin 3 → InfoGeometry.Projective.KleinQuadric.Plucker6 ℂ
  onKlein : ∀ i : Fin 3, InfoGeometry.Projective.KleinQuadric.Plucker6.IsKlein (line i)
  nonincident :
    ∀ {i j : Fin 3}, i ≠ j →
      InfoGeometry.Projective.KleinQuadricIncidence.Plucker6.incidenceForm
        (line i) (line j) ≠ 0

namespace KleinLineConfig3

/-- A pair is on the incidence boundary when the Klein incidence form vanishes. -/
def OnIncidenceBoundary (C : KleinLineConfig3) (i j : Fin 3) : Prop :=
  InfoGeometry.Projective.KleinQuadricIncidence.Plucker6.incidenceForm
    (C.line i) (C.line j) = 0

/-- Pairwise non-incidence forbids the incidence boundary for distinct labels. -/
theorem not_onIncidenceBoundary_of_ne
    (C : KleinLineConfig3) {i j : Fin 3} (hij : i ≠ j) :
    ¬ C.OnIncidenceBoundary i j := by
  exact C.nonincident hij

/-- Non-incidence is symmetric because the Klein incidence pairing is symmetric. -/
theorem nonincident_symm
    (C : KleinLineConfig3) {i j : Fin 3} (hij : i ≠ j) :
    InfoGeometry.Projective.KleinQuadricIncidence.Plucker6.incidenceForm
      (C.line j) (C.line i) ≠ 0 := by
  rw [InfoGeometry.Projective.KleinQuadricIncidence.Plucker6.incidenceForm_symm]
  exact C.nonincident hij

/-- Every line in the packet lies on the Klein quadric. -/
theorem line_isKlein (C : KleinLineConfig3) (i : Fin 3) :
    InfoGeometry.Projective.KleinQuadric.Plucker6.IsKlein (C.line i) :=
  C.onKlein i

end KleinLineConfig3

end Plucker6

/-! ## Amplituhedron / BCFW interfaces -/

/--
Interface for reading Klein line incidence as an amplituhedron boundary.

The implication is supplied data. This file does not construct the
amplituhedron or prove the geometric comparison theorem.
-/
structure AmplituhedronBoundaryInterface
    (C : Plucker6.KleinLineConfig3) where
  boundary : Fin 3 → Fin 3 → Prop
  incidence_to_boundary :
    ∀ {i j : Fin 3}, i ≠ j →
      C.OnIncidenceBoundary i j → boundary i j

/-- Read back a supplied incidence-to-boundary comparison. -/
theorem boundary_of_incidence
    {C : Plucker6.KleinLineConfig3}
    (A : AmplituhedronBoundaryInterface C)
    {i j : Fin 3} (hij : i ≠ j)
    (hinc : C.OnIncidenceBoundary i j) :
    A.boundary i j :=
  A.incidence_to_boundary hij hinc

/--
Interface for comparing an Arnold/cooperad relation with a BCFW recursion step.

This is intentionally a one-way supplied implication.
-/
structure ArnoldBCFWInterface where
  arnoldRelation : Prop
  bcfwRecursion : Prop
  arnold_to_bcfw : arnoldRelation → bcfwRecursion

/-- Read back the supplied Arnold-to-BCFW implication. -/
theorem bcfw_of_arnold
    (A : ArnoldBCFWInterface)
    (hArnold : A.arnoldRelation) :
    A.bcfwRecursion :=
  A.arnold_to_bcfw hArnold

/-! ## Rank-32 budget interface -/

/--
Rank-budget packet for a proposed scattering carrier.

The `stateBudget` field is supplied separately. Matching it to the configured
spin-tiled rank is a finite arithmetic theorem over explicit Betti data.
-/
structure Rank32ScatteringInterface where
  data : ExternalBettiData
  ambient : HasConf3AmbientDimension data
  consistent : RankDataConsistent data
  localRank_eq : data.totalRank = 8
  stateBudget : ℕ
  stateBudget_eq : stateBudget = 32

/-- External local rank `8` plus spin tiling multiplicity `4` matches the supplied `32` budget. -/
theorem spin_tiled_rank_matches_stateBudget
    (R : Rank32ScatteringInterface) :
    R.data.totalRank * spinTilingMultiplicity = R.stateBudget := by
  calc
    R.data.totalRank * spinTilingMultiplicity = 32 :=
      spin_tiled_rank_from_external_data R.data R.ambient R.consistent R.localRank_eq
    _ = R.stateBudget := R.stateBudget_eq.symm

/-! ## Rohozhkin / plabic interface -/

/--
Interface from a completed Rohozhkin pure-braid representation to a chosen
plabic/on-shell move model.

The comparison to plabic moves is explicit data, not a theorem in this file.
-/
structure RohozhkinPlabicInterface (moving : ℕ) where
  packet : RohozhkinProjectiveBraidPacket moving
  PlabicMove : Type
  moveOfGenerator :
    PureBraidGenerator (rohozhkinTotalPoints moving) → PlabicMove

/-- The Rohozhkin component of a plabic interface descends to the presented pure braid group. -/
theorem rohozhkin_plabic_descent_packet {moving : ℕ}
    (P : RohozhkinPlabicInterface moving) :
    ∃ ρ : RohozhkinPureBraidGroup moving →* RohozhkinMatrixUnits moving,
      ∀ g : PureBraidGenerator (rohozhkinTotalPoints moving),
        ρ (of g) = P.packet.delaunay.gen g :=
  rohozhkin_projective_braid_descent_packet P.packet

/--
Combined theorem-safe packet for the twistor/amplituhedron configuration lane.
-/
structure TwistorAmplituhedronBridgeDatum (moving : ℕ) where
  lines : Plucker6.KleinLineConfig3
  boundary : AmplituhedronBoundaryInterface lines
  arnoldBCFW : ArnoldBCFWInterface
  rank : Rank32ScatteringInterface
  rohozhkin : RohozhkinPlabicInterface moving

/-- Combined readback: one selected line is Klein, the rank budget matches `32`,
and the supplied Rohozhkin spec descends to the presented pure braid group. -/
theorem twistor_amplituhedron_bridge_packet {moving : ℕ}
    (D : TwistorAmplituhedronBridgeDatum moving)
    (i : Fin 3) :
    InfoGeometry.Projective.KleinQuadric.Plucker6.IsKlein (D.lines.line i) ∧
      D.rank.data.totalRank * spinTilingMultiplicity = D.rank.stateBudget ∧
      ∃ ρ : RohozhkinPureBraidGroup moving →* RohozhkinMatrixUnits moving,
        ∀ g : PureBraidGenerator (rohozhkinTotalPoints moving),
          ρ (of g) = D.rohozhkin.packet.delaunay.gen g := by
  exact ⟨D.lines.line_isKlein i,
    spin_tiled_rank_matches_stateBudget D.rank,
    rohozhkin_plabic_descent_packet D.rohozhkin⟩

/-- The concrete Penrose projective null twistor space from the twistor owner is inhabited. -/
theorem penrose_projective_null_twistor_nonempty_readback :
    Nonempty PenroseProjectiveNullTwistor :=
  penroseProjectiveNullTwistor_nonempty

/-! ## q-deformation stability interface -/

/-- Kuzmin regime: the complex deformation lies in the open unit disk `|q| < 1`. -/
def inUnitDisk (q : ℂ) : Prop := ‖q‖ < 1

/--
Conservative packet for *assuming* stability of amplituhedron topology under
q-deformation through the Kuzmin corridor, with an explicit q-CCR readout hook.
-/
structure QDeformationStabilityInterface where
  qPacket : KuzminCuntzPathPacket ℂ
  amplituhedronBoundaryRank : ℕ
  qInUnitDisk : inUnitDisk qPacket.q
  boundaryTopologyStable : inUnitDisk qPacket.q → amplituhedronBoundaryRank = 32

/-- Readback: boundary rank is locked to `32` in the supplied stable q-regime. -/
theorem q_deformation_stability_keeps_rank
    (S : QDeformationStabilityInterface) :
    S.amplituhedronBoundaryRank = 32 :=
  S.boundaryTopologyStable S.qInUnitDisk

/--
The `q = 0` endpoint Toeplitz readout transported through the supplied
`toCuntzToeplitz` field, when a q-path packet is available.
-/
theorem q0_toeplitz_readout (S : QDeformationStabilityInterface)
    (h0 : S.qPacket.q = (0 : ℂ))
    (i j : Fin 2) :
    S.qPacket.toCuntzToeplitz (S.qPacket.seed.creation i) *
        S.qPacket.toCuntzToeplitz (S.qPacket.seed.annihilation j) =
      (if i = j then 1 else 0) := by
  have h0' : S.qPacket.seed.q = (0 : ℂ) := by
    simpa [S.qPacket.q_norm] using h0
  simpa using congrArg S.qPacket.toCuntzToeplitz
    (seed_toeplitz_limit (H := S.qPacket.seed) h0' i j)

/--
Conservative zero-boundary package for this lane. The only claim is that `q = 0`
is an explicit readout point inside the supplied unit-disk regimen.
-/
theorem q0_is_in_unit_disk (S : QDeformationStabilityInterface) (h0 : S.qPacket.q = (0 : ℂ)) :
    inUnitDisk S.qPacket.q := by
  have hzero : inUnitDisk (0 : ℂ) := by
    simp [inUnitDisk]
  simpa [h0] using hzero

/--
Boundary readout at `q=0` as a transport theorem from the supplied path packet.
-/
theorem q0_readout_of_stability (S : QDeformationStabilityInterface) (h0 : S.qPacket.q = (0 : ℂ)) (i j : Fin 2) :
    S.qPacket.toCuntzToeplitz (S.qPacket.seed.creation i) *
      S.qPacket.toCuntzToeplitz (S.qPacket.seed.annihilation j) =
    (if i = j then 1 else 0) :=
  q0_toeplitz_readout S h0 i j

/--
The q-deformation datum can be attached to an amplituhedron bridge packet.
-/
structure TwistorAmplituhedronQDeformationBridgeDatum (moving : ℕ) where
  bridge : TwistorAmplituhedronBridgeDatum moving
  deformation : QDeformationStabilityInterface

/-- Combined readout with explicit q-stable rank preservation. -/
theorem twistor_amplituhedron_q_deformation_packet {moving : ℕ}
    (D : TwistorAmplituhedronQDeformationBridgeDatum moving) :
    D.deformation.amplituhedronBoundaryRank = 32 :=
  q_deformation_stability_keeps_rank D.deformation

end InfoGeometry.Projective.TwistorAmplituhedronConfigurationBridge
