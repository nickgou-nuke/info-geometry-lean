import Mathlib.Topology.Basic
import InfoGeometry.Canonical.ColeFurySpinorProjectiveChartTransitions

noncomputable section

namespace InfoGeometry.Canonical.ColeFurySpinorProjectiveAtlas

open InfoGeometry.Algebra.ColeFurySpinorBridge
open InfoGeometry.Canonical.ColeFurySpinorProjectiveTopology
open InfoGeometry.Canonical.ColeFurySpinorProjectiveChart
open InfoGeometry.Canonical.ColeFurySpinorProjectiveChartTransitions

/-- The common domain of three nonzero-coordinate charts. -/
def ChartTriple (i k l : Fin 32) :=
  {ψ : NonzeroSpinor // ψ.1 i ≠ 0 ∧ ψ.1 k ≠ 0 ∧ ψ.1 l ≠ 0}

instance (i k l : Fin 32) : TopologicalSpace (ChartTriple i k l) := by
  change TopologicalSpace
    {ψ : NonzeroSpinor // ψ.1 i ≠ 0 ∧ ψ.1 k ≠ 0 ∧ ψ.1 l ≠ 0}
  infer_instance

/-- The scale factor from the `i` chart to the `k` chart. -/
def scaleFactor (i k : Fin 32) (ψ : ChartOverlap i k) : ℝ :=
  ψ.1.1 k / ψ.1.1 i

theorem continuous_scaleFactor (i k : Fin 32) :
    Continuous (scaleFactor i k) := by
  have hval : Continuous (fun ψ : ChartOverlap i k => ψ.1.1) :=
    continuous_subtype_val.comp continuous_subtype_val
  apply Continuous.div
  · exact (continuous_apply k).comp hval
  · exact (continuous_apply i).comp hval
  · intro ψ
    exact ψ.2.1

/-- Cocycle law for scale factors on the `i,k,l` triple overlap. -/
theorem scaleFactor_cocycle (i k l : Fin 32)
    (ψ : ChartTriple i k l) :
    ψ.1.1 l / ψ.1.1 i =
      (ψ.1.1 l / ψ.1.1 k) * (ψ.1.1 k / ψ.1.1 i) := by
  field_simp [ψ.2.1, ψ.2.2.1, ψ.2.2.2]

end InfoGeometry.Canonical.ColeFurySpinorProjectiveAtlas
