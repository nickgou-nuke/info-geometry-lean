import InfoGeometry.Canonical.RealBdGDIIIAtom
import InfoGeometry.OperatorAlgebra.MoorePenroseDivisionRank
import InfoGeometry.Quantum.BulkBoundary

/-!
# InfoGeometry.Canonical.DIIIDrazinEntropyBridge

Thin bridge from the repo-owned DIII / `ZMod 2` bulk-boundary lane to the
Drazin--Moore--Penrose entropy calibration.

This file does not construct a quaternionic matrix model and does not prove a
division-algebra classification theorem. It records the theorem-safe chain:

* `topologicalIndexZ2 chain = 1` plus a simplified boundary model gives a
  boundary zero-mode property via `Quantum.BulkBoundary`;
* a model-supplied division-fiber calibration identifies the MP projector with
  the localized division-block identity;
* with an explicitly supplied validity proof, faithful trace of that identity
  gives entropy nonnegativity.
-/

noncomputable section

namespace InfoGeometry.Canonical.DIIIDrazinEntropyBridge

open InfoGeometry.Quantum.KitaevChain
open InfoGeometry.Quantum.RealMajorana
open InfoGeometry.Quantum.BulkBoundary
open InfoGeometry.OperatorAlgebra.MoorePenroseDivisionRank

variable {S : Type*}
variable [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
variable [FiniteDimensional ℝ S]

local notation "EndS" => S →L[ℝ] S

/--
DIII `ZMod 2` entropy bridge packet.

The topology side is repo-owned by `Quantum.BulkBoundary`. The entropy side is
repo-owned by `MoorePenroseDivisionRank`. The only new data is the calibration
that the topological sector state is the division fiber used by the entropy
readout.
-/
structure DIIIZ2DivisionEntropyBridge
    (M : RealMajoranaDatum (S := S))
    (P0 : KPolarization (S := S) M)
    (Op State : Type*) [Add Op] [Mul Op] where
  /-- Local open-chain operator channel. -/
  localOp : KitaevCell -> EndS
  /-- Finite Kitaev chain. -/
  chain : List KitaevCell
  /-- Nontrivial `ZMod 2` topological sector. -/
  topologicalIndexZ2_eq_one :
    topologicalIndexZ2 chain = 1
  /-- Boundary model sufficient for the existing bulk-boundary zero-mode theorem. -/
  simplifiedBoundaryModel :
    SimplifiedBoundaryModel (M := M) (P0 := P0) localOp chain
  /-- Drazin/MP division-rank entropy calibration. -/
  divisionEntropy :
    MoorePenroseDivisionIdentityLaw Op State
  /-- State representing this DIII topological sector in the entropy calibration. -/
  stateOfChain : State
  /--
  The nontrivial DIII topological sector has localized to the division fiber
  used by the MP-rank entropy calibration.
  -/
  divisionFiber_of_topologicalSector :
    divisionEntropy.faithfulTrace.isDivisionAlgebraFiber stateOfChain
  /--
  The DIII sector state is represented nontrivially in the metric/operator
  carrier used by the MP-rank entropy calibration.
  -/
  representedNontrivially_of_topologicalSector :
    divisionEntropy.faithfulTrace.representedNontrivially stateOfChain

namespace DIIIZ2DivisionEntropyBridge

variable {M : RealMajoranaDatum (S := S)}
variable {P0 : KPolarization (S := S) M}
variable {Op State : Type*} [Add Op] [Mul Op]
variable (B : DIIIZ2DivisionEntropyBridge (S := S) M P0 Op State)

/-- The nontrivial DIII sector has a surface zero mode. -/
theorem hasSurfaceZeroMode :
    HasZeroMode
      (S := S)
      (globalChainOperatorFromOpenChain (S := S) B.localOp B.chain) :=
  hasSurfaceZeroMode_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel
    (M := M) (P0 := P0)
    B.localOp B.chain
    B.topologicalIndexZ2_eq_one
    B.simplifiedBoundaryModel

omit [CompleteSpace S] [FiniteDimensional ℝ S] in
/--
The DIII division-fiber calibration makes the sector entropy nonnegative.
-/
theorem entropy_nonneg_of_DIII_Z2_sector
    (hvalid : B.divisionEntropy.calibration.functional.readout.valid B.stateOfChain) :
    0 ≤ B.divisionEntropy.calibration.functional.entropy B.stateOfChain :=
  MoorePenroseDivisionIdentityLaw.entropy_nonneg_of_division_identity B.divisionEntropy
    B.stateOfChain
    hvalid
    B.divisionFiber_of_topologicalSector
    B.representedNontrivially_of_topologicalSector

omit [CompleteSpace S] [FiniteDimensional ℝ S] in
/--
The same sector entropy is the logarithm of the MP trace/rank readout.
-/
theorem entropy_eq_log_mp_trace_of_DIII_Z2_sector
    (hvalid : B.divisionEntropy.calibration.functional.readout.valid B.stateOfChain) :
    B.divisionEntropy.calibration.functional.entropy B.stateOfChain =
      B.divisionEntropy.calibration.functional.kB *
        Real.log
          (B.divisionEntropy.calibration.trace
            (B.divisionEntropy.calibration.mpProjector B.stateOfChain)) :=
  MoorePenroseVolumeCalibration.entropy_eq_log_mp_trace B.divisionEntropy.calibration
    B.stateOfChain
    hvalid

/--
The finite static bridge, stated without overclaiming:

* the nontrivial DIII/`ZMod 2` sector supplies a boundary zero-mode property;
* the supplied nontrivially represented division-fiber calibration makes the
  corresponding MP/Drazin entropy nonnegative.
-/
theorem DIII_Z2_boundary_zero_mode_and_entropy_nonneg
    (hvalid : B.divisionEntropy.calibration.functional.readout.valid B.stateOfChain) :
    HasZeroMode
      (S := S)
      (globalChainOperatorFromOpenChain (S := S) B.localOp B.chain)
      ∧
    0 ≤ B.divisionEntropy.calibration.functional.entropy B.stateOfChain :=
  ⟨hasSurfaceZeroMode B, entropy_nonneg_of_DIII_Z2_sector B hvalid⟩

end DIIIZ2DivisionEntropyBridge

end InfoGeometry.Canonical.DIIIDrazinEntropyBridge
