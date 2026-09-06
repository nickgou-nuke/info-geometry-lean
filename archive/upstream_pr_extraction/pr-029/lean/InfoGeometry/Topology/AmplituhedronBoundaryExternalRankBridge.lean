import InfoGeometry.Projective.NonIsoConf3RankIngestion
import InfoGeometry.Topology.AmplituhedronBoundaryRank32

/-!
# External Rank Data to Rank-32 Boundary Carrier

This file connects the explicit external Betti-data arithmetic from
`NonIsoConf3RankIngestion` to the finite `Fin 32` boundary carrier.

Closed here:

* if external data has ambient dimension `8`, is internally consistent, and has
  local rank `8`, then its spin-tiled rank equals the cardinality of
  `BoundaryRank32State`;
* the current candidate local Betti vector satisfies that finite arithmetic;
* a rank-32 boundary realization can carry such external rank evidence.

Not closed here:

* no theorem says the external vector is the actual de Rham cohomology of
  `F_Q(C^4,3)`;
* no theorem says the `Fin 32` carrier is a cohomology basis;
* no theorem says the carrier is an `N = 4` SYM multiplet.
-/

namespace InfoGeometry.Topology.AmplituhedronBoundary

open InfoGeometry.Projective.NonIsoConf3RankIngestion
open InfoGeometry.Projective.PenroseSpinTiling

/-- Explicit external rank evidence sufficient to match the finite `Fin 32` carrier. -/
abbrev ExternalRank32BoundaryCertificate : Type :=
  Σ' data : ExternalBettiData,
    HasConf3AmbientDimension data ∧
      RankDataConsistent data ∧
        data.totalRank = 8

namespace ExternalRank32BoundaryCertificate

abbrev data (C : ExternalRank32BoundaryCertificate) : ExternalBettiData :=
  C.1

abbrev ambient (C : ExternalRank32BoundaryCertificate) :
    HasConf3AmbientDimension C.data :=
  C.2.1

abbrev consistent (C : ExternalRank32BoundaryCertificate) :
    RankDataConsistent C.data :=
  C.2.2.1

abbrev localRank_eq (C : ExternalRank32BoundaryCertificate) :
    C.data.totalRank = 8 :=
  C.2.2.2

end ExternalRank32BoundaryCertificate

/--
The spin-tiled external rank equals the cardinality of the finite rank-32
boundary carrier.
-/
theorem external_spin_tiled_rank_eq_boundary_card
    (C : ExternalRank32BoundaryCertificate) :
    C.data.totalRank * spinTilingMultiplicity =
      Fintype.card BoundaryRank32State := by
  calc
    C.data.totalRank * spinTilingMultiplicity = 32 :=
      spin_tiled_rank_from_external_data C.data C.ambient C.consistent C.localRank_eq
    _ = Fintype.card BoundaryRank32State := by
      exact boundaryRank32State_card.symm

/-- The candidate local Betti vector matches the finite boundary carrier cardinality. -/
theorem candidate_spin_tiled_rank_eq_boundary_card :
    candidateLocalBettiData.totalRank * spinTilingMultiplicity =
      Fintype.card BoundaryRank32State := by
  calc
    candidateLocalBettiData.totalRank * spinTilingMultiplicity = 32 :=
      candidateLocalBettiData_spinTiled_rank32
    _ = Fintype.card BoundaryRank32State := by
      exact boundaryRank32State_card.symm

/--
A rank-32 boundary realization with attached external rank evidence.

This remains a data bridge; it does not assert that `carrierReadout` is a de Rham
basis.
-/
structure ExternalRank32BoundaryRealization (Op : Type*) [Ring Op]
    extends Rank32BoundaryRealization Op where
  cert : ExternalRank32BoundaryCertificate

end InfoGeometry.Topology.AmplituhedronBoundary
