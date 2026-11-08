import InfoGeometry.Quantum.BulkBoundary
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.BulkBoundaryZeroModeOwner

Canonical dimension-agnostic owner surface for boundary-localized operator zero
modes.

The finite-dimensional `finrank` mismatch lane in `Quantum.BulkBoundary` still
matters for index/regularization work, but the more primitive bulk-boundary
payload is simpler:

- an explicit boundary-localized zero-mode witness,
- a resulting operator-level kernel witness,
- hence a genuine nontrivial kernel of the open-chain operator.

This file promotes that witness-first lane into a theorem-facing owner packet so
downstream modules can depend on the dimension-agnostic operator statement
without reconstructing it from local chain data each time.
-/

namespace InfoGeometry.Canonical.BulkBoundaryZeroModeOwner

open InfoGeometry.Krein
open InfoGeometry.Quantum.BulkBoundary
open InfoGeometry.Quantum.KitaevChain
open InfoGeometry.Quantum.RealMajorana

section Core

variable {S : Type*}
variable [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]

local notation "EndS" => S →L[ℝ] S

/-- Canonical owner packet for a dimension-agnostic bulk-boundary zero mode. -/
@[rep_depth operator]
structure DimensionAgnosticBoundaryZeroModeOwner
    (M : RealMajoranaDatum (S := S))
    (P0 : KPolarization (S := S) M)
    (localOp : KitaevCell → EndS)
    (chain : List KitaevCell) where
  boundaryWitness :
    BoundaryLocalizedZeroModeWitness (M := M) (P0 := P0) localOp chain

namespace DimensionAgnosticBoundaryZeroModeOwner

variable {M : RealMajoranaDatum (S := S)}
variable {P0 : KPolarization (S := S) M}
variable {localOp : KitaevCell → EndS}
variable {chain : List KitaevCell}

end DimensionAgnosticBoundaryZeroModeOwner

/-- Canonical kernel readout from the promoted owner packet. -/
theorem owner_hasZeroMode
    {M : RealMajoranaDatum (S := S)}
    {P0 : KPolarization (S := S) M}
    {localOp : KitaevCell → EndS}
    {chain : List KitaevCell}
    (O : DimensionAgnosticBoundaryZeroModeOwner
      (S := S) M P0 localOp chain) :
    HasZeroMode (S := S)
      (globalChainOperatorFromOpenChain (S := S) localOp chain) := by
  exact hasZeroMode_of_operatorZeroModeWitness (S := S)
    (operatorZeroModeWitnessOfBoundaryLocalizedPlus
      (M := M) (P0 := P0) localOp chain O.boundaryWitness)

/-- Canonical explicit zero-mode readout from the promoted owner packet. -/
theorem owner_exists_zeroMode
    {M : RealMajoranaDatum (S := S)}
    {P0 : KPolarization (S := S) M}
    {localOp : KitaevCell → EndS}
    {chain : List KitaevCell}
    (O : DimensionAgnosticBoundaryZeroModeOwner
      (S := S) M P0 localOp chain) :
    ∃ v : S,
      (globalChainOperatorFromOpenChain (S := S) localOp chain) v = 0 ∧ v ≠ 0 := by
  exact exists_zeroMode_of_operatorZeroModeWitness (S := S)
    (operatorZeroModeWitnessOfBoundaryLocalizedPlus
      (M := M) (P0 := P0) localOp chain O.boundaryWitness)

/--
Canonical constructor from the simplified-boundary-model negative-phase lane.
-/
@[rep_depth operator]
noncomputable def owner_of_negativePhase_of_simplifiedBoundaryModel
    (M : RealMajoranaDatum (S := S))
    (P0 : KPolarization (S := S) M)
    (localOp : KitaevCell → EndS)
    (chain : List KitaevCell)
    (hNeg : topologicalIndex chain = -1)
    (hSimple : SimplifiedBoundaryModel (M := M) (P0 := P0) localOp chain) :
    DimensionAgnosticBoundaryZeroModeOwner
      (S := S) M P0 localOp chain where
  boundaryWitness :=
    boundaryLocalizedZeroModeWitness_of_negativePhase_of_simplifiedBoundaryModel
      (M := M) (P0 := P0) localOp chain hNeg hSimple

/--
Canonical constructor from the turnkey `topologicalIndexZ2 = 1` lane.
-/
@[rep_depth operator]
noncomputable def owner_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel
    (M : RealMajoranaDatum (S := S))
    (P0 : KPolarization (S := S) M)
    (localOp : KitaevCell → EndS)
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hSimple : SimplifiedBoundaryModel (M := M) (P0 := P0) localOp chain) :
    DimensionAgnosticBoundaryZeroModeOwner
      (S := S) M P0 localOp chain where
  boundaryWitness :=
    boundaryLocalizedZeroModeWitness_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel
      (M := M) (P0 := P0) localOp chain hTopo hSimple

/--
Promoted dimension-agnostic bulk-boundary theorem:
the simplified boundary model already yields a genuine operator kernel.
-/
theorem hasZeroMode_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel
    (M : RealMajoranaDatum (S := S))
    (P0 : KPolarization (S := S) M)
    (localOp : KitaevCell → EndS)
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hSimple : SimplifiedBoundaryModel (M := M) (P0 := P0) localOp chain) :
    HasZeroMode (S := S)
      (globalChainOperatorFromOpenChain (S := S) localOp chain) := by
  let O :=
    owner_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel
      (S := S) M P0 localOp chain hTopo hSimple
  exact owner_hasZeroMode O

/--
Promoted explicit witness theorem for the same dimension-agnostic lane.
-/
theorem exists_zeroMode_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel
    (M : RealMajoranaDatum (S := S))
    (P0 : KPolarization (S := S) M)
    (localOp : KitaevCell → EndS)
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hSimple : SimplifiedBoundaryModel (M := M) (P0 := P0) localOp chain) :
    ∃ v : S,
      (globalChainOperatorFromOpenChain (S := S) localOp chain) v = 0 ∧ v ≠ 0 := by
  let O :=
    owner_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel
      (S := S) M P0 localOp chain hTopo hSimple
  exact owner_exists_zeroMode O

end Core

end InfoGeometry.Canonical.BulkBoundaryZeroModeOwner
