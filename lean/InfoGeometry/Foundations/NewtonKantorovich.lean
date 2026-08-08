import Mathlib.Tactic
import InfoGeometry.Foundations.NewtonKantorovichBase
import InfoGeometry.Foundations.NewtonKantorovichRoots
import InfoGeometry.Foundations.NewtonKantorovichSequence
import InfoGeometry.Foundations.NewtonKantorovichCertificate

/-!
# InfoGeometry.Foundations.NewtonKantorovich

Focused Newton--Kantorovich property layer for the scalar majorant lane.
-/

namespace InfoGeometry.Foundations.NewtonKantorovich

open InfoGeometry.Foundations.NewtonKantorovichBase
open InfoGeometry.Foundations.NewtonKantorovichRoots
open InfoGeometry.Foundations.NewtonKantorovichSequence
open InfoGeometry.Foundations.NewtonKantorovichCertificate

noncomputable section

/-- Safety form of the half-threshold: `h ≤ 1/2 ⟹ 0 ≤ 1 - 2h`. -/
theorem h_safe (h : ℝ) (hh : h ≤ (1 / 2 : ℝ)) :
    0 ≤ 1 - 2 * h := by
  linarith

/--
Nonnegativity of a majorant step on `[0, tMinus]` under strict
Kantorovich hypotheses.
-/
theorem majorant_step_nonneg
    (L η t : ℝ)
    (hL : 0 < L)
    (_hη : 0 ≤ η)
    (hcond : L * η < 1 / 2)
    (ht : t ∈ Set.Icc 0 (tMinus L η)) :
    0 ≤ majorantStep L η t := by
  have hΔ : 0 ≤ discriminant L η := by
    unfold discriminant
    linarith
  have hΔpos : 0 < discriminant L η := by
    unfold discriminant
    linarith
  have hP : 0 ≤ P L η t := (P_nonneg_on_Icc_zero_tMinus L η hL hΔ) t ht
  have hstep_ge_t : t ≤ majorantStep L η t :=
    step_ge_of_P_nonneg_on_left_interval L η t hL ht.2 hΔpos hP
  linarith [ht.1, hstep_ge_t]

/--
Monotonicity of the shifted majorant sequence `n ↦ t_{n+1}` under strict
Kantorovich assumptions.
-/
theorem majorant_step_mono_on_interval
    (L η : ℝ)
    (hL : 0 < L)
    (hη : 0 ≤ η)
    (hcond : L * η < 1 / 2) :
    ∀ n, majorantSeq L η (n + 1) ≤ majorantSeq L η (n + 2) := by
  exact (majorantSeq_mem_and_monotone_of_kantorovich_strict L η hL hη hcond).2

/--
Residual contraction (nonincreasing residual to `tMinus`) on the property
interval.
-/
theorem majorant_step_contractive_on_interval
    (L η t : ℝ)
    (hL : 0 < L)
    (_hη : 0 ≤ η)
    (hcond : L * η < 1 / 2)
    (ht : t ∈ Set.Icc 0 (tMinus L η)) :
    tMinus L η - majorantStep L η t ≤ tMinus L η - t := by
  have hΔ : 0 ≤ discriminant L η := by
    unfold discriminant
    linarith
  have hΔpos : 0 < discriminant L η := by
    unfold discriminant
    linarith
  exact nk_one_step_residual_nonincreasing L η t hL hΔ hΔpos ht

/--
Geometric-step criterion: if step distances of the shifted majorant sequence
are bounded by `C * q^n` with `q < 1`, then the shifted sequence is Cauchy.
-/
theorem majorant_seq_cauchy_of_h_le_half
    (L η C q : ℝ)
    (_hcond : L * η ≤ 1 / 2)
    (hq : q < 1)
    (hstep :
      ∀ n,
        dist (majorantSeq L η (n + 1)) (majorantSeq L η (n + 2)) ≤ C * q ^ n) :
    CauchySeq (fun n => majorantSeq L η (n + 1)) := by
  exact cauchySeq_of_le_geometric q C hq hstep

end
end InfoGeometry.Foundations.NewtonKantorovich
