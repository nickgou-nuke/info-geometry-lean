import Mathlib.Topology.Basic
import InfoGeometry.Canonical.ColeFurySpinorProjectiveChart

noncomputable section

namespace InfoGeometry.Canonical.ColeFurySpinorProjectiveChartTransitions

open InfoGeometry.Algebra.ColeFurySpinorBridge
open InfoGeometry.Canonical.ColeFurySpinorProjectiveTopology
open InfoGeometry.Canonical.ColeFurySpinorProjectiveChart

/-- The overlap of the `i`- and `k`-coordinate charts. -/
def ChartOverlap (i k : Fin 32) :=
  {ψ : NonzeroSpinor // ψ.1 i ≠ 0 ∧ ψ.1 k ≠ 0}

instance (i k : Fin 32) : TopologicalSpace (ChartOverlap i k) := by
  change TopologicalSpace {ψ : NonzeroSpinor // ψ.1 i ≠ 0 ∧ ψ.1 k ≠ 0}
  infer_instance

def overlapToChart (i k : Fin 32) (ψ : ChartOverlap i k) : CoordinateChart i :=
  ⟨ψ.1, ψ.2.1⟩

def overlapToChartK (i k : Fin 32) (ψ : ChartOverlap i k) : CoordinateChart k :=
  ⟨ψ.1, ψ.2.2⟩

/-- The affine transition map on the `i,k` overlap. -/
def transitionMap (i j k : Fin 32) (ψ : ChartOverlap i k) : ℝ :=
  coordinateRatio k j (overlapToChartK i k ψ) *
    coordinateRatio i k (overlapToChart i k ψ)

theorem chart_transition_formula (i j k : Fin 32) (ψ : ChartOverlap i k) :
    coordinateRatio i j (overlapToChart i k ψ) = transitionMap i j k ψ := by
  change ψ.1.1 j / ψ.1.1 i =
    (ψ.1.1 j / ψ.1.1 k) * (ψ.1.1 k / ψ.1.1 i)
  field_simp [ψ.2.1, ψ.2.2]

theorem continuous_transitionMap (i j k : Fin 32) :
    Continuous (transitionMap i j k) := by
  have hval : Continuous (fun ψ : ChartOverlap i k => ψ.1.1) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hji : Continuous (fun ψ : ChartOverlap i k => ψ.1.1 j) :=
    (continuous_apply j).comp hval
  have hki : Continuous (fun ψ : ChartOverlap i k => ψ.1.1 k) :=
    (continuous_apply k).comp hval
  have hii : Continuous (fun ψ : ChartOverlap i k => ψ.1.1 i) :=
    (continuous_apply i).comp hval
  have hleft : Continuous (fun ψ : ChartOverlap i k => ψ.1.1 j / ψ.1.1 k) := by
    apply Continuous.div hji hki
    intro ψ
    exact ψ.2.2
  have hright : Continuous (fun ψ : ChartOverlap i k => ψ.1.1 k / ψ.1.1 i) := by
    apply Continuous.div hki hii
    intro ψ
    exact ψ.2.1
  exact hleft.mul hright

end InfoGeometry.Canonical.ColeFurySpinorProjectiveChartTransitions
