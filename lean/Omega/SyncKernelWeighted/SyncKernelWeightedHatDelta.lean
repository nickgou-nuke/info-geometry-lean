import Omega.SyncKernelWeighted.PrimitiveCompletionHatp
import Omega.SyncKernelWeighted.WeightedCompletionQ

namespace Omega.SyncKernelWeighted

open Omega.UnitCirclePhaseArithmetic
open scoped Polynomial

/-- The concrete unit-parameter instance of the completed weighted Laurent identity. -/
def sync_kernel_weighted_hat_delta_unit_statement : Prop :=
  weightedCompletionLaurent (1 : ℝ)⁻¹ 1 = weightedCompletionLaurent 1 1 ∧
    (weightedCompletionSextic (1 * 1) (1 ^ 2) = 0 ↔
      weightedCompletionQ (1 + (1 : ℝ)⁻¹) 1 = 0) ∧
      (weightedCompletionSextic (1 * 1) (1 ^ 2) = 0 ↔
        weightedCompletionQ (2 * Real.cosh (0 / 2)) 1 = 0) ∧
        Real.log (1 * 1) = 0 / 2 + Real.log 1

/-- The primitive-completion proposition exposed by the imported owner theorem. -/
def sync_kernel_weighted_hat_delta_primitive_statement : Prop :=
  (∀ n : ℕ, 1 ≤ n →
      ∃ P : Polynomial ℤ,
        ∀ r : ℚ, r ≠ 0 →
          completionEval P (r + r⁻¹) = completionEval P (r⁻¹ + r)) ∧
    (∀ n : ℕ, primitive_completion_hatp_parity_statement n) ∧
      (∀ d : ℕ, chebyshevTraceFormula d)

/-- Paper label: `prop:sync-kernel-weighted-hat-delta`.
This wrapper touches the completed Laurent invariance under `r ↦ r⁻¹` and the descended
polynomial package in the trace coordinate on concrete unit data. -/
theorem paper_sync_kernel_weighted_hat_delta :
    sync_kernel_weighted_hat_delta_unit_statement ∧
      sync_kernel_weighted_hat_delta_primitive_statement := by
  have hWeighted := paper_weighted_completion_q 1 1 0 one_ne_zero (by norm_num) (by simp)
  have hPrimitive := paper_primitive_completion_hatp
  exact ⟨by simpa [sync_kernel_weighted_hat_delta_unit_statement] using hWeighted,
    by simpa [sync_kernel_weighted_hat_delta_primitive_statement] using hPrimitive⟩

end Omega.SyncKernelWeighted
