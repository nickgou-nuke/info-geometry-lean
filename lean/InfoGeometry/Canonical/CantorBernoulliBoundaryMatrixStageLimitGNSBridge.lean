import InfoGeometry.Canonical.CantorBernoulliBoundaryMatrixStageLimitBridge
import InfoGeometry.Canonical.CantorBernoulliBoundaryRangeGNSBridge

/-!
# Matrix-stage limit trace and the native gauge-GNS readout

This bridge compares the canonical algebraic matrix-stage limit with the
already existing finite boundary-range trace and native filtered GNS readout.
It identifies their scalar value on each common finite stage only.  It does
not identify the matrix-stage quotient with the separate filtered C⋆ direct
limit, and it does not identify the spatial boundary vector state with the
gauge state.
-/

namespace InfoGeometry.Canonical.CantorBernoulliBoundaryMatrixStageLimitGNSBridge

open InfoGeometry.Canonical.MatrixStageInductiveLimit
open InfoGeometry.Canonical.CantorBernoulliBoundaryMatrixStageLimitBridge
open InfoGeometry.Canonical.CantorBernoulliBoundaryRangeGNSBridge
open InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge
open InfoGeometry.Canonical.GenuineMatrixStageMorphism
open InfoGeometry.Canonical.ComplexMatrixStage
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open CStarStateColimit.Native.FilteredGNSGlobalStageRepresentation
open InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalHilbertSchmidt
open InfoGeometry.Canonical.CantorBernoulliGaugeFilteredGNSColimitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStageTransportBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveBernoulliMeasure
open MeasureTheory
open scoped ComplexOrder InnerProductSpace

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

theorem limitTrace_stage_eq_boundaryRangeTrace
    (n : ℕ) (A : ComplexMatrixStage.Stage n) :
    limitTrace (canonicalStageHom n A) =
      boundaryRangeTrace n (boundaryRangeElement n A) := by
  rw [canonicalStageHom_apply, limitTrace_toLimit,
    boundaryRangeTrace_stage,
    normalizedTrace_apply,
    bitWordMatrixTraceFunctional_apply]
  have hcard : Fintype.card (BitWord n) = 2 ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  rw [hcard]
  norm_num

theorem limitTrace_stage_eq_gaugeGNS_readout
    (n : ℕ) (A : ComplexMatrixStage.Stage n) :
    limitTrace (canonicalStageHom n A) =
      ⟪gaugeGNSColimitVacuum,
        globalStageRepresentationStarAlgHom
          gaugeStage gaugeSystem gaugeStateFamily n
          (CStarMatrix.ofMatrixStarAlgEquiv
            (bitWordStageStarAlgEquiv n A))
          gaugeGNSColimitVacuum⟫_ℂ := by
  rw [limitTrace_stage_eq_boundaryRangeTrace]
  exact boundaryRangeTrace_gaugeGNS_readout n A

theorem limitTrace_stage_eq_projectiveDiagonalReadout
    (n : ℕ) (A : ComplexMatrixStage.Stage n) :
    limitTrace (canonicalStageHom n A) =
      ∫ q, diagonalPart n A (π n q) ∂projectiveLimitMeasure := by
  rw [limitTrace_stage_eq_boundaryRangeTrace]
  exact boundaryRangeTrace_projectiveDiagonalReadout n A

end

end InfoGeometry.Canonical.CantorBernoulliBoundaryMatrixStageLimitGNSBridge
