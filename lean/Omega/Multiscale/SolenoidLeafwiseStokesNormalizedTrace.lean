import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import Omega.Multiscale.NormalizedStokesFiniteCoverInverseTower
import Omega.Multiscale.NormalizedStokesTraceL1Completion
import Omega.Multiscale.SolenoidStokesRadonMeasureRealization

namespace Omega.Multiscale

open Filter Topology
open NormalizedStokesFiniteCoverInverseTowerSystem

/-- Concrete carriers for the normalized-trace realization on a circle covering tower. -/
structure SolenoidLeafwiseStokesNormalizedTraceData where
  coverSystem : NormalizedStokesFiniteCoverInverseTowerSystem
  traceData : NormalizedStokesTraceL1CompletionData
  radonData : SolenoidStokesRadonMeasureData
  baseLevel : radonData.Level

private theorem tendsto_of_abs_sub_le
    {u : ℕ → ℝ} {L : ℝ} {b : ℕ → ℝ}
    (hBound : ∀ n, |L - u n| ≤ b n)
    (hTail : Tendsto b atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 L) := by
  have hNorm :
      Tendsto (fun n => ‖u n - L‖) atTop (𝓝 0) := by
    have hAbs :
        Tendsto (fun n => |L - u n|) atTop (𝓝 0) :=
      squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) (Eventually.of_forall hBound)
        hTail
    simpa [Real.norm_eq_abs, abs_sub_comm] using hAbs
  exact tendsto_iff_norm_sub_tendsto_zero.2 hNorm

/-- The normalized trace is realized by a Radon probability measure and the leafwise Stokes
functional vanishes when the finite-level boundaries are empty. -/
theorem paper_app_solenoid_leafwise_stokes_normalized_trace
    (D : SolenoidLeafwiseStokesNormalizedTraceData)
    (traceDefect_eq_normalizedDifferential :
      D.traceData.normalizedDefect = normalizedDifferential D.coverSystem)
    (circleBoundaryEmpty : ∀ n, D.coverSystem.boundaryIntegral n = 0)
    (normalizedTrace_mass_one : D.traceData.extensionValue = 1)
    (realizedBaseMass_eq_boundaryLimit :
      D.radonData.inverseLimitCylinderMass D.baseLevel = D.traceData.boundaryLimit)
    (layerwiseStokes :
      ∀ n, D.traceData.normalizedBulk n - D.traceData.normalizedBoundary n =
        D.traceData.normalizedDefect n)
    (bulk_tail :
      ∀ n, |D.traceData.bulkLimit - D.traceData.normalizedBulk n| ≤
        D.traceData.bulkTailBound n)
    (boundary_tail :
      ∀ n, |D.traceData.boundaryLimit - D.traceData.normalizedBoundary n| ≤
        D.traceData.boundaryTailBound n)
    (defect_tail :
      ∀ n, |D.traceData.defectLimit - D.traceData.normalizedDefect n| ≤
        D.traceData.defectTailBound n)
    (bulkTail_tendsto_zero : Tendsto D.traceData.bulkTailBound atTop (𝓝 0))
    (boundaryTail_tendsto_zero : Tendsto D.traceData.boundaryTailBound atTop (𝓝 0))
    (defectTail_tendsto_zero : Tendsto D.traceData.defectTailBound atTop (𝓝 0))
    (boundary_eventually_stable :
      ∀ n, D.traceData.stableIndex ≤ n →
        D.traceData.normalizedBoundary n = D.traceData.stableValue)
    (trace_respects_tail :
      ∀ u v : ℕ → ℝ, (∃ N, ∀ n, N ≤ n → u n = v n) →
        D.traceData.traceFunctional u = D.traceData.traceFunctional v)
    (trace_on_constant :
      ∀ c : ℝ, D.traceData.traceFunctional (fun _ => c) = c)
    (trace_on_boundary :
      D.traceData.traceFunctional D.traceData.normalizedBoundary = D.traceData.extensionValue) :
    D.radonData.compatiblePushforwards ∧
      D.radonData.l1ExtensionOfStokesFunctional ∧
        D.radonData.inverseLimitCylinderMass D.baseLevel = 1 ∧
          D.traceData.defectLimit = 0 := by
  rcases paper_app_solenoid_stokes_radon_measure_realization D.radonData with
    ⟨hPush, _, hL1⟩
  rcases paper_app_normalized_stokes_trace_l1_completion D.traceData layerwiseStokes bulk_tail
      boundary_tail defect_tail bulkTail_tendsto_zero boundaryTail_tendsto_zero
      defectTail_tendsto_zero boundary_eventually_stable trace_respects_tail trace_on_constant
      trace_on_boundary with
    ⟨_, _, hUnique⟩
  have hMass : D.radonData.inverseLimitCylinderMass D.baseLevel = 1 := by
    calc
      D.radonData.inverseLimitCylinderMass D.baseLevel = D.traceData.boundaryLimit :=
        realizedBaseMass_eq_boundaryLimit
      _ = D.traceData.extensionValue := by symm; exact hUnique
      _ = 1 := normalizedTrace_mass_one
  have hDiffBoundary :
      ∀ n,
        normalizedDifferential D.coverSystem n = normalizedBoundary D.coverSystem n := by
    rcases paper_app_normalized_stokes_finite_cover_inverse_tower D.coverSystem with
      ⟨_, _, _, hLevelwise⟩
    exact hLevelwise
  have hBoundaryZero : ∀ n, normalizedBoundary D.coverSystem n = 0 := by
    intro n
    rw [normalizedBoundary, circleBoundaryEmpty n]
    simp
  have hDifferentialZero : ∀ n, normalizedDifferential D.coverSystem n = 0 := by
    intro n
    rw [hDiffBoundary n, hBoundaryZero n]
  have hTraceDefectZero : ∀ n, D.traceData.normalizedDefect n = 0 := by
    intro n
    rw [traceDefect_eq_normalizedDifferential]
    exact hDifferentialZero n
  have hTraceDefectTendsto :
      Tendsto D.traceData.normalizedDefect atTop (𝓝 D.traceData.defectLimit) :=
    tendsto_of_abs_sub_le defect_tail defectTail_tendsto_zero
  have hZeroTendsto : Tendsto D.traceData.normalizedDefect atTop (𝓝 0) := by
    have hZeroFun : D.traceData.normalizedDefect = fun _ => (0 : ℝ) := by
      funext n
      exact hTraceDefectZero n
    rw [hZeroFun]
    exact tendsto_const_nhds
  have hLeafwise : D.traceData.defectLimit = 0 :=
    tendsto_nhds_unique hTraceDefectTendsto hZeroTendsto
  exact ⟨hPush, hL1, hMass, hLeafwise⟩

end Omega.Multiscale
