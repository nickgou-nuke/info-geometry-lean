import InfoGeometry.Canonical.CuntzMatrixTraceTopologicalGNSBridge
import InfoGeometry.Canonical.CuntzMatrixTowerColimitBridge

/-!
# Finite Cuntz projection readouts in the topological matrix colimit

The rectangular frame gives two concrete range projections in the first matrix
stage.  This owner transports their already-proved normalized trace values
through the real trace cocone and the topological colimit injections.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzMatrixProjectionTopologicalReadout

open InfoGeometry.Canonical.CuntzMatrixTraceTopologicalGNSBridge
open InfoGeometry.Canonical.CuntzMatrixTowerColimitBridge
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixTraceTopologicalColimit
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation

theorem realTrace_colimit_projection1
    (T : InfoGeometry.Canonical.CuntzMatrixTraceTower.Data) :
    realTraceTopologicalColimitMap T
        (topologicalInclusion T 1 cuntzStage1_S1) = (1 / 2 : ℝ) := by
  rw [realTraceTopologicalColimitMap_inclusion]
  have h := congrArg Complex.re cuntzStage1_trace_S1
  simpa [matrixTraceState, matrixTraceFunctional_apply] using h

theorem realTrace_colimit_projection2
    (T : InfoGeometry.Canonical.CuntzMatrixTraceTower.Data) :
    realTraceTopologicalColimitMap T
        (topologicalInclusion T 1 cuntzStage1_S2) = (1 / 2 : ℝ) := by
  rw [realTraceTopologicalColimitMap_inclusion]
  have h := congrArg Complex.re cuntzStage1_trace_S2
  simpa [matrixTraceState, matrixTraceFunctional_apply] using h

end InfoGeometry.Canonical.CuntzMatrixProjectionTopologicalReadout
