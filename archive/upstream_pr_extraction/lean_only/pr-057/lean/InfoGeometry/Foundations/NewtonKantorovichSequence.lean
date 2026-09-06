import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import InfoGeometry.Foundations.NewtonKantorovichBase
import InfoGeometry.Foundations.NewtonKantorovichRoots

/-!
# InfoGeometry.Foundations.NewtonKantorovichSequence

Executable Newton--Kantorovich majorant step and first sequence-level lemmas.
-/

namespace InfoGeometry.Foundations.NewtonKantorovichSequence

open InfoGeometry.Foundations.NewtonKantorovichBase
open NewtonKantorovichRoots

noncomputable section

/-- Majorant Newton step written in denominator form. -/
def majorantStep (L η t : ℝ) : ℝ :=
  (η - (L / 2) * t^2) / (1 - L * t)

/-- `P'(t)` as `-(1 - Lt)`. -/
theorem P_deriv_eq_neg_one_sub (L t : ℝ) :
    P_deriv L t = -(1 - L * t) := by
  unfold P_deriv
  ring

/-- Bridge from Newton form `t - P/P'` to `majorantStep`. -/
theorem majorantStep_eq_newton (L η t : ℝ) (h_deriv : P_deriv L t ≠ 0) :
    majorantStep L η t = t - (P L η t) / (P_deriv L t) := by
  unfold majorantStep
  symm
  exact newton_step_identity L η t h_deriv

/-- Value of the majorant step at `0`. -/
theorem majorantStep_at_zero (L η : ℝ) :
    majorantStep L η 0 = η := by
  unfold majorantStep
  ring

/-- Denominator at `tMinus` is nonzero when `Δ > 0`. -/
theorem one_sub_L_tMinus_ne_zero_of_discriminant_pos
    (L η : ℝ) (hL : L ≠ 0) (hΔpos : 0 < discriminant L η) :
    1 - L * tMinus L η ≠ 0 := by
  rw [one_sub_L_tMinus L η hL]
  unfold sqrtDiscriminant
  exact Real.sqrt_ne_zero'.2 hΔpos

/-- `P'(tMinus) ≠ 0` when `Δ > 0`. -/
theorem P_deriv_tMinus_ne_zero_of_discriminant_pos
    (L η : ℝ) (hL : L ≠ 0) (hΔpos : 0 < discriminant L η) :
    P_deriv L (tMinus L η) ≠ 0 := by
  rw [P_deriv_eq_neg_one_sub]
  exact neg_ne_zero.2 (one_sub_L_tMinus_ne_zero_of_discriminant_pos L η hL hΔpos)

/-- `tMinus` is a fixed point of the Newton majorant step when `Δ > 0`. -/
theorem majorantStep_tMinus_fixed
    (L η : ℝ) (hL : L ≠ 0) (hΔ : 0 ≤ discriminant L η) (hΔpos : 0 < discriminant L η) :
    majorantStep L η (tMinus L η) = tMinus L η := by
  have hderiv : P_deriv L (tMinus L η) ≠ 0 :=
    P_deriv_tMinus_ne_zero_of_discriminant_pos L η hL hΔpos
  calc
    majorantStep L η (tMinus L η)
        = tMinus L η - (P L η (tMinus L η)) / (P_deriv L (tMinus L η)) := by
            exact majorantStep_eq_newton L η (tMinus L η) hderiv
    _ = tMinus L η - 0 / (P_deriv L (tMinus L η)) := by rw [P_tMinus_eq_zero L η hL hΔ]
    _ = tMinus L η := by ring

/-- Explicit recursive majorant sequence with start `t₀ = 0`. -/
def majorantSeq (L η : ℝ) : Nat → ℝ
  | 0 => 0
  | n + 1 => majorantStep L η (majorantSeq L η n)

@[simp] theorem majorantSeq_zero (L η : ℝ) : majorantSeq L η 0 = 0 := rfl

@[simp] theorem majorantSeq_succ (L η : ℝ) (n : Nat) :
    majorantSeq L η (n + 1) = majorantStep L η (majorantSeq L η n) := rfl

/-- First iterate equals `η`. -/
theorem majorantSeq_one (L η : ℝ) :
    majorantSeq L η 1 = η := by
  simp [majorantStep_at_zero]

/-- Nonnegativity of `tMinus` under the standard Kantorovich assumptions. -/
theorem tMinus_nonneg_of_kantorovich
    (L η : ℝ) (hL : 0 < L) (hη : 0 ≤ η) (hcond : L * η ≤ 1 / 2) :
    0 ≤ tMinus L η := by
  have hΔnonneg : 0 ≤ discriminant L η :=
    (kantorovich_condition_iff_discriminant_nonneg L η).1 hcond
  have hLη_nonneg : 0 ≤ L * η := mul_nonneg hL.le hη
  have hΔ_le_one : discriminant L η ≤ 1 := by
    unfold discriminant
    nlinarith
  have hsqrt_le_one : sqrtDiscriminant L η ≤ 1 := by
    unfold sqrtDiscriminant
    exact (Real.sqrt_le_iff).2 ⟨by positivity, by simpa using hΔ_le_one⟩
  unfold tMinus
  have hnum : 0 ≤ 1 - sqrtDiscriminant L η := by linarith
  exact div_nonneg hnum hL.le

/-- Under Kantorovich assumptions, `η` is below the small majorant root. -/
theorem eta_le_tMinus_of_kantorovich
    (L η : ℝ) (hL : 0 < L) (hη : 0 ≤ η) (hcond : L * η ≤ 1 / 2) :
    η ≤ tMinus L η := by
  have hΔnonneg : 0 ≤ discriminant L η :=
    (kantorovich_condition_iff_discriminant_nonneg L η).1 hcond
  have hLη_nonneg : 0 ≤ L * η := mul_nonneg hL.le hη
  have h_rhs_nonneg : 0 ≤ 1 - L * η := by linarith
  have hdisc_le_sq : discriminant L η ≤ (1 - L * η)^2 := by
    unfold discriminant
    nlinarith
  have hsqrt_le : sqrtDiscriminant L η ≤ 1 - L * η := by
    unfold sqrtDiscriminant
    exact (Real.sqrt_le_iff).2 ⟨h_rhs_nonneg, hdisc_le_sq⟩
  unfold tMinus
  rw [le_div_iff₀ hL]
  linarith

/-- First iterate belongs to `[0, tMinus]` under Kantorovich assumptions. -/
theorem majorantSeq_one_mem_Icc_zero_tMinus
    (L η : ℝ) (hL : 0 < L) (hη : 0 ≤ η) (hcond : L * η ≤ 1 / 2) :
    majorantSeq L η 1 ∈ Set.Icc 0 (tMinus L η) := by
  constructor
  · rw [majorantSeq_one]
    exact hη
  · rw [majorantSeq_one]
    exact eta_le_tMinus_of_kantorovich L η hL hη hcond

/--
If the majorant step preserves `[0, tMinus]` and `η` is inside this interval,
then every iterate is inside `[0, tMinus]`.
-/
theorem majorantSeq_mem_Icc_of_step_invariant
    (L η : ℝ)
    (hη_mem : η ∈ Set.Icc 0 (tMinus L η))
    (hInv : ∀ t, t ∈ Set.Icc 0 (tMinus L η) →
      majorantStep L η t ∈ Set.Icc 0 (tMinus L η)) :
    ∀ n, majorantSeq L η (n + 1) ∈ Set.Icc 0 (tMinus L η) := by
  intro n
  induction n with
  | zero =>
      simpa [majorantSeq_succ, majorantSeq_zero, majorantStep_at_zero] using hη_mem
  | succ n ih =>
      simpa [majorantSeq_succ] using hInv (majorantSeq L η (n + 1)) ih

/--
If the majorant step is pointwise expansive on `[0, tMinus]` and iterates stay
in that interval, then the sequence is monotone increasing.
-/
theorem majorantSeq_monotone_of_step_ge
    (L η : ℝ)
    (hmem : ∀ n, majorantSeq L η (n + 1) ∈ Set.Icc 0 (tMinus L η))
    (hStepGe : ∀ t, t ∈ Set.Icc 0 (tMinus L η) → t ≤ majorantStep L η t) :
    ∀ n, majorantSeq L η (n + 1) ≤ majorantSeq L η (n + 2) := by
  intro n
  have hn : majorantSeq L η (n + 1) ∈ Set.Icc 0 (tMinus L η) := hmem n
  have hge := hStepGe (majorantSeq L η (n + 1)) hn
  simpa [majorantSeq_succ] using hge

/--
Concrete Kantorovich wrapper:
if one has a step-invariance proof on `[0, tMinus]`, then every iterate
`t_{n+1}` stays in `[0, tMinus]`.
-/
theorem majorantSeq_mem_Icc_of_kantorovich
    (L η : ℝ) (hL : 0 < L) (hη : 0 ≤ η) (hcond : L * η ≤ 1 / 2)
    (hInv : ∀ t, t ∈ Set.Icc 0 (tMinus L η) →
      majorantStep L η t ∈ Set.Icc 0 (tMinus L η)) :
    ∀ n, majorantSeq L η (n + 1) ∈ Set.Icc 0 (tMinus L η) := by
  have hη_mem : η ∈ Set.Icc 0 (tMinus L η) := by
    simpa [majorantSeq_one, majorantStep_at_zero] using
      (majorantSeq_one_mem_Icc_zero_tMinus L η hL hη hcond)
  exact majorantSeq_mem_Icc_of_step_invariant L η hη_mem hInv

/--
Concrete Kantorovich monotonicity wrapper:
given step-invariance and pointwise step-expansiveness on `[0, tMinus]`,
the sequence is monotone increasing from index `1`.
-/
theorem majorantSeq_monotone_of_kantorovich
    (L η : ℝ) (hL : 0 < L) (hη : 0 ≤ η) (hcond : L * η ≤ 1 / 2)
    (hInv : ∀ t, t ∈ Set.Icc 0 (tMinus L η) →
      majorantStep L η t ∈ Set.Icc 0 (tMinus L η))
    (hStepGe : ∀ t, t ∈ Set.Icc 0 (tMinus L η) → t ≤ majorantStep L η t) :
    ∀ n, majorantSeq L η (n + 1) ≤ majorantSeq L η (n + 2) := by
  have hmem : ∀ n, majorantSeq L η (n + 1) ∈ Set.Icc 0 (tMinus L η) :=
    majorantSeq_mem_Icc_of_kantorovich L η hL hη hcond hInv
  exact majorantSeq_monotone_of_step_ge L η hmem hStepGe

/-- Closed-form expression for the second majorant iterate. -/
theorem majorantSeq_two_formula (L η : ℝ) :
    majorantSeq L η 2 = (η - (L / 2) * η^2) / (1 - L * η) := by
  simp [majorantSeq_succ, majorantStep]

/-- Strict Kantorovich threshold gives a strictly positive denominator at `η`. -/
theorem one_sub_L_mul_eta_pos_of_kantorovich_strict
    (L η : ℝ) (hcond : L * η < 1 / 2) :
    0 < 1 - L * η := by
  linarith

/-- Under standard nonnegativity assumptions, the second iterate is nonnegative. -/
theorem majorantSeq_two_nonneg_of_kantorovich
    (L η : ℝ) (hL : 0 ≤ L) (hη : 0 ≤ η) (hcond : L * η ≤ 1 / 2) :
    0 ≤ majorantSeq L η 2 := by
  rw [majorantSeq_two_formula]
  have hden : 0 < 1 - L * η := by linarith
  apply div_nonneg
  · have hLη_nonneg : 0 ≤ L * η := mul_nonneg hL hη
    have hfac_nonneg : 0 ≤ 1 - (L * η) / 2 := by linarith
    calc
      0 ≤ η * (1 - (L * η) / 2) := mul_nonneg hη hfac_nonneg
      _ = η - (L / 2) * η^2 := by ring
  · exact hden.le

/-- First monotonic step: `t₁ ≤ t₂` under strict Kantorovich threshold. -/
theorem majorantSeq_one_le_two_of_kantorovich_strict
    (L η : ℝ) (hL : 0 ≤ L) (_hη : 0 ≤ η) (hcond : L * η < 1 / 2) :
    majorantSeq L η 1 ≤ majorantSeq L η 2 := by
  rw [majorantSeq_one, majorantSeq_two_formula]
  have hden : 0 < 1 - L * η := one_sub_L_mul_eta_pos_of_kantorovich_strict L η hcond
  rw [le_div_iff₀ hden]
  calc
    η * (1 - L * η) ≤ η - (L / 2) * η^2 := by
      have hcore : (L / 2) * η^2 ≤ L * η^2 := by
        have hhalf : (1 : ℝ) / 2 ≤ 1 := by norm_num
        calc
          (L / 2) * η^2 = L * η^2 * ((1 : ℝ) / 2) := by ring
          _ ≤ L * η^2 * 1 := by gcongr
          _ = L * η^2 := by ring
      linarith
    _ = η - (L / 2) * η^2 := rfl

/--
Strict denominator positivity on `[0, tMinus]` under strict Kantorovich threshold.
-/
theorem one_sub_L_mul_pos_of_mem_Icc_zero_tMinus_strict
    (L η t : ℝ) (hL : 0 < L) (hcond : L * η < 1 / 2)
    (ht : t ∈ Set.Icc 0 (tMinus L η)) :
    0 < 1 - L * t := by
  rcases ht with ⟨_ht0, ht1⟩
  have hLt_le : L * t ≤ L * tMinus L η := by
    exact mul_le_mul_of_nonneg_left ht1 hL.le
  -- use exact strict denominator at `tMinus`
  have htm : 1 - L * tMinus L η = sqrtDiscriminant L η :=
    one_sub_L_tMinus L η (ne_of_gt hL)
  have hΔpos : 0 < discriminant L η := by
    unfold discriminant
    linarith
  have hden_tm : 0 < 1 - L * tMinus L η := by
    rw [htm]
    unfold sqrtDiscriminant
    exact Real.sqrt_pos.2 hΔpos
  have hden_ge : 1 - L * t ≥ 1 - L * tMinus L η := by linarith
  exact lt_of_lt_of_le hden_tm hden_ge

/--
Step-growth reduction on `[0, tMinus]`:
if `P(t) ≥ 0`, then `t ≤ majorantStep(t)` (strict NK denominator branch).
-/
theorem step_ge_of_P_nonneg_on_Icc_zero_tMinus_strict
    (L η t : ℝ) (hL : 0 < L) (hcond : L * η < 1 / 2)
    (ht : t ∈ Set.Icc 0 (tMinus L η))
    (hP : 0 ≤ P L η t) :
    t ≤ majorantStep L η t := by
  have hden_pos : 0 < 1 - L * t :=
    one_sub_L_mul_pos_of_mem_Icc_zero_tMinus_strict L η t hL hcond ht
  have hmain : majorantStep L η t - t = (P L η t) / (1 - L * t) := by
    unfold majorantStep P
    field_simp [ne_of_gt hden_pos]
    ring
  have hfrac_nonneg : 0 ≤ (P L η t) / (1 - L * t) := div_nonneg hP hden_pos.le
  have hstep_nonneg : 0 ≤ majorantStep L η t - t := by
    rw [hmain]
    exact hfrac_nonneg
  linarith

/--
Combined sequence package:
from interval invariance and local expansivity of the step, obtain both
boundedness in `[0, tMinus]` and monotone growth of all positive iterates.
-/
theorem majorantSeq_mem_and_monotone_of_step_properties
    (L η : ℝ)
    (hη_mem : η ∈ Set.Icc 0 (tMinus L η))
    (hInv : ∀ t, t ∈ Set.Icc 0 (tMinus L η) →
      majorantStep L η t ∈ Set.Icc 0 (tMinus L η))
    (hStepGe : ∀ t, t ∈ Set.Icc 0 (tMinus L η) → t ≤ majorantStep L η t) :
    (∀ n, majorantSeq L η (n + 1) ∈ Set.Icc 0 (tMinus L η)) ∧
    (∀ n, majorantSeq L η (n + 1) ≤ majorantSeq L η (n + 2)) := by
  constructor
  · exact majorantSeq_mem_Icc_of_step_invariant L η hη_mem hInv
  ·
    intro n
    have hmem_all : ∀ k, majorantSeq L η (k + 1) ∈ Set.Icc 0 (tMinus L η) :=
      majorantSeq_mem_Icc_of_step_invariant L η hη_mem hInv
    exact majorantSeq_monotone_of_step_ge L η hmem_all hStepGe n

/-- Algebraic identity: majorant step increment equals `P / (1 - Lt)`. -/
theorem majorantStep_sub_self_eq_P_div (L η t : ℝ) (hden : 1 - L * t ≠ 0) :
    majorantStep L η t - t = P L η t / (1 - L * t) := by
  unfold majorantStep P
  field_simp [hden]
  ring

/-- Positivity of denominator at `tMinus` under strict discriminant. -/
theorem one_sub_L_tMinus_pos_of_discriminant_pos
    (L η : ℝ) (hL : L ≠ 0) (hΔpos : 0 < discriminant L η) :
    0 < 1 - L * tMinus L η := by
  rw [one_sub_L_tMinus L η hL]
  unfold sqrtDiscriminant
  exact Real.sqrt_pos.2 hΔpos

/--
If `0 < L` and `t ≤ tMinus`, then the Newton denominator is positive.
-/
theorem one_sub_L_t_pos_of_le_tMinus
    (L η t : ℝ) (hL : 0 < L) (ht : t ≤ tMinus L η) (hΔpos : 0 < discriminant L η) :
    0 < 1 - L * t := by
  have hL0 : L ≠ 0 := ne_of_gt hL
  have htm : 0 < 1 - L * tMinus L η :=
    one_sub_L_tMinus_pos_of_discriminant_pos L η hL0 hΔpos
  have hLt_le : L * t ≤ L * tMinus L η := by gcongr
  linarith

/--
Local monotonicity step: if `P(t) ≥ 0` and `t ≤ tMinus`, then `t ≤ majorantStep(t)`.
-/
theorem step_ge_of_P_nonneg_on_left_interval
    (L η t : ℝ)
    (hL : 0 < L)
    (ht : t ≤ tMinus L η)
    (hΔpos : 0 < discriminant L η)
    (hP : 0 ≤ P L η t) :
    t ≤ majorantStep L η t := by
  have hden_pos : 0 < 1 - L * t := one_sub_L_t_pos_of_le_tMinus L η t hL ht hΔpos
  have hden_ne : 1 - L * t ≠ 0 := ne_of_gt hden_pos
  have hinc : majorantStep L η t - t = P L η t / (1 - L * t) :=
    majorantStep_sub_self_eq_P_div L η t hden_ne
  have hq : 0 ≤ P L η t / (1 - L * t) := div_nonneg hP hden_pos.le
  have h0 : 0 ≤ majorantStep L η t - t := by simpa [hinc] using hq
  linarith

/--
Interval-wise expansivity from interval-wise nonnegativity of `P`.
-/
theorem step_ge_on_Icc_of_P_nonneg
    (L η : ℝ)
    (hL : 0 < L)
    (hΔpos : 0 < discriminant L η)
    (hPnonneg : ∀ t, t ∈ Set.Icc 0 (tMinus L η) → 0 ≤ P L η t) :
    ∀ t, t ∈ Set.Icc 0 (tMinus L η) → t ≤ majorantStep L η t := by
  intro t ht
  exact step_ge_of_P_nonneg_on_left_interval L η t hL ht.2 hΔpos (hPnonneg t ht)

/--
If one has explicit lower/upper interval bounds for the step map on `[0, tMinus]`,
then one gets interval invariance in `Set.Icc` form.
-/
theorem step_invariant_of_step_bounds
    (L η : ℝ)
    (hLower : ∀ t, t ∈ Set.Icc 0 (tMinus L η) → 0 ≤ majorantStep L η t)
    (hUpper : ∀ t, t ∈ Set.Icc 0 (tMinus L η) → majorantStep L η t ≤ tMinus L η) :
    ∀ t, t ∈ Set.Icc 0 (tMinus L η) →
      majorantStep L η t ∈ Set.Icc 0 (tMinus L η) := by
  intro t ht
  exact ⟨hLower t ht, hUpper t ht⟩

/-- Newton correction term `Δ = -P/P'` at the scalar majorant lane. -/
def nkCorrection (L η t : ℝ) : ℝ :=
  - (P L η t) / (P_deriv L t)

/-- Majorant update as base-point plus Newton correction. -/
theorem majorantStep_eq_t_add_nkCorrection
    (L η t : ℝ) (h_deriv : P_deriv L t ≠ 0) :
    majorantStep L η t = t + nkCorrection L η t := by
  unfold nkCorrection
  have hstep : majorantStep L η t = t - (P L η t) / (P_deriv L t) :=
    majorantStep_eq_newton L η t h_deriv
  calc
    majorantStep L η t = t - (P L η t) / (P_deriv L t) := hstep
    _ = t + (-(P L η t) / (P_deriv L t)) := by ring

/-- If `Δa` is chosen as the NK correction, the update is exactly `t + Δa`. -/
theorem majorantStep_eq_t_add_of_correction
    (L η t Δa : ℝ) (h_deriv : P_deriv L t ≠ 0)
    (hΔ : Δa = nkCorrection L η t) :
    majorantStep L η t = t + Δa := by
  rw [hΔ]
  exact majorantStep_eq_t_add_nkCorrection L η t h_deriv

/--
Lower interval bound from step expansivity:
if `t ≤ majorantStep t` on `[0, tMinus]`, then `0 ≤ majorantStep t` there.
-/
theorem step_lower_bound_of_step_ge
    (L η : ℝ)
    (hStepGe : ∀ t, t ∈ Set.Icc 0 (tMinus L η) → t ≤ majorantStep L η t) :
    ∀ t, t ∈ Set.Icc 0 (tMinus L η) → 0 ≤ majorantStep L η t := by
  intro t ht
  have h0t : 0 ≤ t := ht.1
  have htstep : t ≤ majorantStep L η t := hStepGe t ht
  linarith

/--
Concrete NK sequence package from:
1. strict denominator branch (`0 < L`, `Δ > 0`),
2. intervalwise nonnegativity of `P`,
3. intervalwise upper bound `majorantStep t ≤ tMinus`,
4. initial point `η ∈ [0, tMinus]`.

This discharges all sequence-level obligations except the local upper-step
inequality.
-/
theorem majorantSeq_mem_and_monotone_of_P_nonneg_and_step_upper
    (L η : ℝ)
    (hL : 0 < L)
    (hΔpos : 0 < discriminant L η)
    (hη_mem : η ∈ Set.Icc 0 (tMinus L η))
    (hPnonneg : ∀ t, t ∈ Set.Icc 0 (tMinus L η) → 0 ≤ P L η t)
    (hUpper : ∀ t, t ∈ Set.Icc 0 (tMinus L η) → majorantStep L η t ≤ tMinus L η) :
    (∀ n, majorantSeq L η (n + 1) ∈ Set.Icc 0 (tMinus L η)) ∧
    (∀ n, majorantSeq L η (n + 1) ≤ majorantSeq L η (n + 2)) := by
  have hStepGe : ∀ t, t ∈ Set.Icc 0 (tMinus L η) → t ≤ majorantStep L η t :=
    step_ge_on_Icc_of_P_nonneg L η hL hΔpos hPnonneg
  have hLower : ∀ t, t ∈ Set.Icc 0 (tMinus L η) → 0 ≤ majorantStep L η t :=
    step_lower_bound_of_step_ge L η hStepGe
  have hInv : ∀ t, t ∈ Set.Icc 0 (tMinus L η) →
      majorantStep L η t ∈ Set.Icc 0 (tMinus L η) :=
    step_invariant_of_step_bounds L η hLower hUpper
  exact majorantSeq_mem_and_monotone_of_step_properties L η hη_mem hInv hStepGe

/-- Read `η` from the root equation `P(tMinus)=0`. -/
theorem eta_eq_tMinus_sub_half_L_sq
    (L η : ℝ) (hL : L ≠ 0) (hΔ : 0 ≤ discriminant L η) :
    η = tMinus L η - (L / 2) * (tMinus L η)^2 := by
  have hroot : P L η (tMinus L η) = 0 := P_tMinus_eq_zero L η hL hΔ
  unfold P at hroot
  linarith

/--
Hard local upper-step inequality on the left interval:
`majorantStep t ≤ tMinus` for `t ≤ tMinus`, under strict denominator branch.
-/
theorem step_upper_on_left_interval
    (L η t : ℝ)
    (hL : 0 < L)
    (ht : t ≤ tMinus L η)
    (hΔ : 0 ≤ discriminant L η)
    (hΔpos : 0 < discriminant L η) :
    majorantStep L η t ≤ tMinus L η := by
  let r : ℝ := tMinus L η
  have hL0 : L ≠ 0 := ne_of_gt hL
  have hr : P L η r = 0 := by
    simpa [r] using P_tMinus_eq_zero L η hL0 hΔ
  have heta : η = r - (L / 2) * r^2 := by
    unfold P at hr
    linarith
  have ht' : t ≤ r := by simpa [r] using ht
  have hden_pos : 0 < 1 - L * t := one_sub_L_t_pos_of_le_tMinus L η t hL ht' hΔpos
  have hsq_nonneg : 0 ≤ (r - t)^2 := sq_nonneg (r - t)
  have hnum_nonpos :
      - (L / 2) * (r - t)^2 ≤ 0 := by
    have hL2 : 0 ≤ L / 2 := by positivity
    nlinarith
  have hdiff :
      majorantStep L η t - r =
        (-(L / 2) * (r - t)^2) / (1 - L * t) := by
    unfold majorantStep
    rw [heta]
    field_simp [ne_of_gt hden_pos]
    ring
  have hfrac_nonpos :
      (-(L / 2) * (r - t)^2) / (1 - L * t) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg hnum_nonpos hden_pos.le
  have hle : majorantStep L η t - r ≤ 0 := by
    simpa [hdiff] using hfrac_nonpos
  have : majorantStep L η t ≤ r := by linarith
  simpa [r] using this

/--
Intervalwise upper bound derived from the local upper-step inequality.
-/
theorem step_upper_on_Icc_zero_tMinus
    (L η : ℝ)
    (hL : 0 < L)
    (hΔ : 0 ≤ discriminant L η)
    (hΔpos : 0 < discriminant L η) :
    ∀ t, t ∈ Set.Icc 0 (tMinus L η) → majorantStep L η t ≤ tMinus L η := by
  intro t ht
  exact step_upper_on_left_interval L η t hL ht.2 hΔ hΔpos

/--
On the left interval `[0, tMinus]`, the majorant polynomial is nonnegative.
-/
theorem P_nonneg_on_Icc_zero_tMinus
    (L η : ℝ)
    (hL : 0 < L)
    (hΔ : 0 ≤ discriminant L η) :
    ∀ t, t ∈ Set.Icc 0 (tMinus L η) → 0 ≤ P L η t := by
  intro t ht
  let r : ℝ := tMinus L η
  have hL0 : L ≠ 0 := ne_of_gt hL
  have hroot : P L η r = 0 := by
    simpa [r] using P_tMinus_eq_zero L η hL0 hΔ
  have heta : η = r - (L / 2) * r^2 := by
    unfold P at hroot
    linarith
  have htr : t ≤ r := by simpa [r] using ht.2
  have hsq_nonneg : 0 ≤ (r - t)^2 := sq_nonneg (r - t)
  have hL2_nonneg : 0 ≤ L / 2 := by positivity
  have hfactor_nonneg : 0 ≤ (L / 2) * (r - t)^2 := mul_nonneg hL2_nonneg hsq_nonneg
  have hform : P L η t = (L / 2) * (r - t)^2 + (1 - L * r) * (r - t) := by
    unfold P
    rw [heta]
    ring
  have hden_r_nonneg : 0 ≤ 1 - L * r := by
    rw [one_sub_L_tMinus L η hL0]
    unfold sqrtDiscriminant
    exact Real.sqrt_nonneg _
  have hdiff_nonneg : 0 ≤ r - t := sub_nonneg.mpr htr
  have hlin_nonneg : 0 ≤ (1 - L * r) * (r - t) := mul_nonneg hden_r_nonneg hdiff_nonneg
  have hsum_nonneg : 0 ≤ (L / 2) * (r - t)^2 + (1 - L * r) * (r - t) := add_nonneg hfactor_nonneg hlin_nonneg
  simpa [hform] using hsum_nonneg

/--
Full NK sequence package under strict Kantorovich hypotheses:
all positive iterates lie in `[0,tMinus]` and are monotone increasing.
-/
theorem majorantSeq_mem_and_monotone_of_kantorovich_strict
    (L η : ℝ)
    (hL : 0 < L)
    (hη : 0 ≤ η)
    (hcond : L * η < 1 / 2) :
    (∀ n, majorantSeq L η (n + 1) ∈ Set.Icc 0 (tMinus L η)) ∧
    (∀ n, majorantSeq L η (n + 1) ≤ majorantSeq L η (n + 2)) := by
  have hΔpos : 0 < discriminant L η := by
    unfold discriminant
    linarith
  have hΔ : 0 ≤ discriminant L η := le_of_lt hΔpos
  have hη_mem : η ∈ Set.Icc 0 (tMinus L η) := by
    constructor
    · exact hη
    · exact eta_le_tMinus_of_kantorovich L η hL hη (le_of_lt hcond)
  have hPnonneg : ∀ t, t ∈ Set.Icc 0 (tMinus L η) → 0 ≤ P L η t :=
    P_nonneg_on_Icc_zero_tMinus L η hL hΔ
  have hUpper : ∀ t, t ∈ Set.Icc 0 (tMinus L η) → majorantStep L η t ≤ tMinus L η :=
    step_upper_on_Icc_zero_tMinus L η hL hΔ hΔpos
  exact majorantSeq_mem_and_monotone_of_P_nonneg_and_step_upper
    L η hL hΔpos hη_mem hPnonneg hUpper

/--
Monotone-bounded envelope of the NK majorant sequence under strict Kantorovich
hypotheses: the shifted sequence `u n = t_{n+1}` is monotone, bounded above,
and has a least upper bound in `ℝ`.
-/
theorem majorantSeq_shifted_has_lub_of_kantorovich_strict
    (L η : ℝ)
    (hL : 0 < L)
    (hη : 0 ≤ η)
    (hcond : L * η < 1 / 2) :
    ∃ ℓ : ℝ,
      IsLUB (Set.range (fun n : ℕ => majorantSeq L η (n + 1))) ℓ := by
  have hpack :=
    majorantSeq_mem_and_monotone_of_kantorovich_strict L η hL hη hcond
  rcases hpack with ⟨hmem, hmonoStep⟩
  let u : ℕ → ℝ := fun n => majorantSeq L η (n + 1)
  have hu_mono : Monotone u := by
    exact monotone_nat_of_le_succ (fun n => by simpa [u] using hmonoStep n)
  have hu_bddAbove : BddAbove (Set.range u) := by
    refine ⟨tMinus L η, ?_⟩
    intro y hy
    rcases hy with ⟨n, rfl⟩
    exact (hmem n).2
  have hu_nonempty : (Set.range u).Nonempty := ⟨u 0, ⟨0, rfl⟩⟩
  rcases Real.exists_isLUB hu_nonempty hu_bddAbove with ⟨ℓ, hℓ⟩
  exact ⟨ℓ, by simpa [u] using hℓ⟩

/--
Any least upper bound `ℓ` of the shifted NK majorant sequence lies in the
explicit envelope `[η, tMinus]` under strict Kantorovich assumptions.
-/
theorem majorantSeq_shifted_lub_bounds_of_kantorovich_strict
    (L η ℓ : ℝ)
    (hL : 0 < L)
    (hη : 0 ≤ η)
    (hcond : L * η < 1 / 2)
    (hℓ : IsLUB (Set.range (fun n : ℕ => majorantSeq L η (n + 1))) ℓ) :
    η ≤ ℓ ∧ ℓ ≤ tMinus L η := by
  have hpack :=
    majorantSeq_mem_and_monotone_of_kantorovich_strict L η hL hη hcond
  rcases hpack with ⟨hmem, _hmonoStep⟩
  have hη_le_lub : η ≤ ℓ := by
    have hη_in : η ∈ Set.range (fun n : ℕ => majorantSeq L η (n + 1)) := by
      refine ⟨0, ?_⟩
      simpa using (majorantSeq_one L η)
    exact hℓ.1 hη_in
  have hlub_le_tminus : ℓ ≤ tMinus L η := by
    exact hℓ.2 (by
      intro y hy
      rcases hy with ⟨n, rfl⟩
      exact (hmem n).2)
  exact ⟨hη_le_lub, hlub_le_tminus⟩

/--
Strict Kantorovich packaging:
there exists a least upper bound `ℓ` of the shifted majorant sequence, and it
lies in the explicit envelope `[η, tMinus]`.
-/
theorem majorantSeq_shifted_exists_lub_in_Icc_of_kantorovich_strict
    (L η : ℝ)
    (hL : 0 < L)
    (hη : 0 ≤ η)
    (hcond : L * η < 1 / 2) :
    ∃ ℓ : ℝ,
      IsLUB (Set.range (fun n : ℕ => majorantSeq L η (n + 1))) ℓ ∧
      η ≤ ℓ ∧ ℓ ≤ tMinus L η := by
  rcases majorantSeq_shifted_has_lub_of_kantorovich_strict L η hL hη hcond with ⟨ℓ, hℓ⟩
  have hbounds :=
    majorantSeq_shifted_lub_bounds_of_kantorovich_strict L η ℓ hL hη hcond hℓ
  exact ⟨ℓ, hℓ, hbounds.1, hbounds.2⟩

end
end InfoGeometry.Foundations.NewtonKantorovichSequence
