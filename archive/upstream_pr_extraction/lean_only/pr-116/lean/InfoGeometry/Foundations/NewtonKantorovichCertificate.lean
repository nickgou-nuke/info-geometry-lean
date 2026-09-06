import InfoGeometry.Foundations.NewtonKantorovichBase
import InfoGeometry.Foundations.NewtonKantorovichRoots
import InfoGeometry.Foundations.NewtonKantorovichSequence

/-!
# InfoGeometry.Foundations.NewtonKantorovichCertificate

Scalar Newton--Kantorovich property packaging layer.

This module re-exports the strict Kantorovich majorant guarantees as a compact
theorem surface for downstream numerical certification.
-/

namespace InfoGeometry.Foundations.NewtonKantorovichCertificate

open InfoGeometry.Foundations.NewtonKantorovichBase
open NewtonKantorovichRoots
open NewtonKantorovichSequence

/-- Discriminant safety under the standard Kantorovich threshold. -/
theorem nk_discriminant_nonneg_of_half_threshold
    (L η : ℝ) (hcond : L * η ≤ 1 / 2) :
    0 ≤ discriminant L η :=
  (kantorovich_condition_iff_discriminant_nonneg L η).1 hcond

/-- Small/large majorant roots are ordered under `h ≤ 1/2`. -/
theorem nk_root_order_of_half_threshold
    (L η : ℝ) (hL : 0 < L) (_hcond : L * η ≤ 1 / 2) :
    tMinus L η ≤ tPlus L η := by
  exact tMinus_le_tPlus L η hL

/--
Strict NK sequence property:
all positive iterates stay in `[0, tMinus]` and are monotone increasing.
-/
theorem nk_shifted_mem_and_monotone
    (L η : ℝ)
    (hL : 0 < L)
    (hη : 0 ≤ η)
    (hcond : L * η < 1 / 2) :
    (∀ n, majorantSeq L η (n + 1) ∈ Set.Icc 0 (tMinus L η)) ∧
    (∀ n, majorantSeq L η (n + 1) ≤ majorantSeq L η (n + 2)) :=
  majorantSeq_mem_and_monotone_of_kantorovich_strict L η hL hη hcond

/--
Strict NK LUB property for the shifted sequence together with explicit bounds.
-/
theorem nk_shifted_exists_lub_in_Icc
    (L η : ℝ)
    (hL : 0 < L)
    (hη : 0 ≤ η)
    (hcond : L * η < 1 / 2) :
    ∃ ℓ : ℝ,
      IsLUB (Set.range (fun n : ℕ => majorantSeq L η (n + 1))) ℓ ∧
      η ≤ ℓ ∧ ℓ ≤ tMinus L η :=
  majorantSeq_shifted_exists_lub_in_Icc_of_kantorovich_strict L η hL hη hcond

/--
One-step residual inequality to the property upper bound `tMinus`.
-/
theorem nk_one_step_residual_nonincreasing
    (L η t : ℝ)
    (hL : 0 < L)
    (hΔ : 0 ≤ discriminant L η)
    (hΔpos : 0 < discriminant L η)
    (ht : t ∈ Set.Icc 0 (tMinus L η)) :
    tMinus L η - majorantStep L η t ≤ tMinus L η - t := by
  have hstep_le : majorantStep L η t ≤ tMinus L η :=
    step_upper_on_left_interval L η t hL ht.2 hΔ hΔpos
  have hstep_ge : t ≤ majorantStep L η t := by
    exact step_ge_of_P_nonneg_on_left_interval L η t hL ht.2 hΔpos
      ((P_nonneg_on_Icc_zero_tMinus L η hL hΔ) t ht)
  linarith

end InfoGeometry.Foundations.NewtonKantorovichCertificate
