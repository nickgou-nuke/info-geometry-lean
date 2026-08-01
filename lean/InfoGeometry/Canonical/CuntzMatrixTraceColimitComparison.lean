import InfoGeometry.Canonical.CuntzMatrixTraceTopologicalColimit

/-!
# Stagewise comparison of algebraic and topological trace colimits

The `ModuleCat` and `TopCat` colimits of the matrix tower are distinct
categorical constructions.  Their canonical trace readouts nevertheless
agree exactly on every finite-stage representative.  This is the honest
comparison square available before choosing any topology on the algebraic
colimit carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzMatrixTraceColimitComparison

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixTraceTopologicalColimit
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation

@[simp] theorem trace_readout_agrees_on_stage
    (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T n A) = matrixTraceState n A)
    (n : ℕ) (A : MatrixStage n) :
    traceColimitFunctional T hT (traceColimitInclusion T n A) =
      traceTopologicalColimitMap T hT (topologicalInclusion T n A) := by
  rw [traceColimitFunctional_inclusion T hT,
    traceTopologicalColimitMap_inclusion T hT]

theorem trace_readout_agrees_on_transition
    (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T n A) = matrixTraceState n A)
    {m n : ℕ} (hmn : m ≤ n) (A : MatrixStage m) :
    traceTopologicalColimitMap T hT
        (topologicalInclusion T n (map T hmn A)) =
      traceColimitFunctional T hT (traceColimitInclusion T m A) := by
  rw [topologicalInclusion_transition]
  rw [traceTopologicalColimitMap_inclusion T hT,
    traceColimitFunctional_inclusion T hT]

theorem trace_readout_is_stage_independent
    (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T n A) = matrixTraceState n A)
    {m n : ℕ} (hmn : m ≤ n) (A : MatrixStage m) :
    traceTopologicalColimitMap T hT
        (topologicalInclusion T n (map T hmn A)) =
      traceTopologicalColimitMap T hT (topologicalInclusion T m A) := by
  rw [topologicalInclusion_transition]

end InfoGeometry.Canonical.CuntzMatrixTraceColimitComparison
