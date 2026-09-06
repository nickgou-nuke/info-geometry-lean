import Mathlib.Tactic
import InfoGeometry.External.Auto.KanCayley
import InfoGeometry.External.Auto.ComplexTemperatureRH
import InfoGeometry.External.Auto.LieFlowCompilerBridge
import InfoGeometry.External.Auto.uhf_cantor_boundary

/-!
  Honest extracted theorem seeds from `/home/goutev/g&t.txt`.

  This file keeps only theorem-backed statements that are actually discharged
  by the mirror or by the local mathlib proof below.  It does not retain the
  original placeholder carrier zoo or the false target stubs.
-/

namespace GT.Extracted

/-- Codebase-backed version of `theorem exponential_reconstruction_surjective`. -/
theorem exponential_reconstruction_surjective
    {G X V : Type*} [Group G] [MulAction G X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (C : InfoGeometry.Canonical.LieFlowCompiler.KMSCompiler G X V) :
    Function.Surjective C.chart.exp := by
  exact InfoGeometry.Canonical.LieFlowCompiler.KMSCompiler.exp_surjective C

/-- The diagonal UHF boundary is canonically identified with binary strings. -/
theorem crystallization_unifies_continuum :
    Nonempty (CantorBoundary ≃ (ℕ → Bool)) := by
  exact ⟨cantor_is_diagonal_spectrum⟩

/-- The thermal Cayley coordinate tends to the boundary point `1`. -/
theorem thermal_cayley_tendto_boundary_one :
    Filter.Tendsto (fun β : ℝ => (β - 1) / (β + 1)) Filter.atTop (nhds (1 : ℝ)) := by
  have hden :
      Filter.Tendsto (fun β : ℝ => β + 1) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b, ?_⟩
    intro β hβ
    linarith
  have hzero :
      Filter.Tendsto (fun β : ℝ => (2 : ℝ) / (β + 1)) Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop hden
  have hmain :
      Filter.Tendsto (fun β : ℝ => 1 - (2 : ℝ) / (β + 1))
        Filter.atTop (nhds (1 - 0 : ℝ)) :=
    tendsto_const_nhds.sub hzero
  have heq :
      (fun β : ℝ => (β - 1) / (β + 1)) =ᶠ[Filter.atTop]
        fun β : ℝ => 1 - (2 : ℝ) / (β + 1) := by
    filter_upwards [Filter.eventually_gt_atTop (-1 : ℝ)] with β hβ
    have hβ' : β + 1 ≠ 0 := by linarith
    field_simp [hβ']
    ring
  simpa using hmain.congr' heq.symm

/-- The critical balance line of the complex-temperature chart is the midpoint. -/
theorem criticalBalanceLine_complexTemperature_GT (β t : ℝ) :
    criticalBalanceLine (complexTemperature β t) ↔ β = 1 / 2 := by
  exact criticalBalanceLine_complexTemperature β t

end GT.Extracted
