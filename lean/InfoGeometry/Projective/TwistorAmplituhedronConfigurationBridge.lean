import InfoGeometry.Projective.KleinQuadricIncidence
import InfoGeometry.Projective.NonIsoConf3RankIngestion
import InfoGeometry.Projective.RohozhkinDelaunayScramblingBridge
import InfoGeometry.Projective.Twistor.Incidence
import InfoGeometry.Projective.KuzminCuntzPath
import InfoGeometry.Topology.AmplituhedronBoundary

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
open InfoGeometry.Topology.AmplituhedronBoundary

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
def AmplituhedronBoundaryInterface
    (C : Plucker6.KleinLineConfig3) : Type _ :=
  {boundary : Fin 3 → Fin 3 → Prop //
    ∀ {i j : Fin 3}, i ≠ j →
      C.OnIncidenceBoundary i j → boundary i j}

namespace AmplituhedronBoundaryInterface

/-- Native subtype projection for the boundary predicate. -/
abbrev boundary
    {C : Plucker6.KleinLineConfig3}
    (A : AmplituhedronBoundaryInterface C) : Fin 3 → Fin 3 → Prop :=
  A.1

/-- Native subtype proof of incidence-to-boundary containment. -/
theorem incidence_to_boundary
    {C : Plucker6.KleinLineConfig3}
    (A : AmplituhedronBoundaryInterface C)
    {i j : Fin 3} (hij : i ≠ j)
    (hinc : C.OnIncidenceBoundary i j) :
    A.boundary i j :=
  A.2 hij hinc

end AmplituhedronBoundaryInterface

/-- Read back a supplied incidence-to-boundary comparison. -/
theorem boundary_of_incidence
    {C : Plucker6.KleinLineConfig3}
    (A : AmplituhedronBoundaryInterface C)
    {i j : Fin 3} (hij : i ≠ j)
    (hinc : C.OnIncidenceBoundary i j) :
    A.boundary i j :=
  A.incidence_to_boundary hij hinc

/--
The native three-point Arnold--BCFW carrier is the Arnold--Cohen quotient
algebra.  Its boundary packet stores actual ring elements and a proved
cooperad/BCFW equality, rather than two unrelated proposition markers.
-/
abbrev ThreePointArnoldAlgebra :=
  RingQuot
    (InfoGeometry.Projective.Amplituhedron.ArnoldRel ℤ (Fin 3))

/-- Genuine operator-valued Arnold/BCFW comparison packet. -/
abbrev ArnoldBCFWInterface :=
  AmplituhedronBoundaryPacket ThreePointArnoldAlgebra

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
        ρ (of g) = InfoGeometry.Projective.RohozhkinDelaunayScramblingBridge.rohozhkinProjectiveBraidPacketGen P.packet g :=
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

/-- Native readouts for the Klein-line, rank-budget, and braid-descent lanes. -/
theorem twistor_line_isKlein {moving : ℕ}
    (D : TwistorAmplituhedronBridgeDatum moving) (i : Fin 3) :
    InfoGeometry.Projective.KleinQuadric.Plucker6.IsKlein (D.lines.line i) :=
  D.lines.line_isKlein i

theorem twistor_rank_budget {moving : ℕ}
    (D : TwistorAmplituhedronBridgeDatum moving) :
    D.rank.data.totalRank * spinTilingMultiplicity = D.rank.stateBudget :=
  spin_tiled_rank_matches_stateBudget D.rank

theorem twistor_rohozhkin_descent {moving : ℕ}
    (D : TwistorAmplituhedronBridgeDatum moving) :
    ∃ ρ : RohozhkinPureBraidGroup moving →* RohozhkinMatrixUnits moving,
      ∀ g : PureBraidGenerator (rohozhkinTotalPoints moving),
        ρ (of g) = InfoGeometry.Projective.RohozhkinDelaunayScramblingBridge.rohozhkinProjectiveBraidPacketGen D.rohozhkin.packet g :=
  rohozhkin_plabic_descent_packet D.rohozhkin

/-- The concrete Penrose projective null twistor space from the twistor owner is inhabited. -/
theorem penrose_projective_null_twistor_nonempty_readback :
    Nonempty PenroseProjectiveNullTwistor :=
  penroseProjectiveNullTwistor_nonempty

end InfoGeometry.Projective.TwistorAmplituhedronConfigurationBridge
