import Mathlib.Tactic

noncomputable section

namespace SarkarTwoLevelIsospinMixing

def observedGap (E1 E2 : ℚ) : ℚ :=
  E2 - E1

def H11 (E1 E2 b2 : ℚ) : ℚ :=
  E1 + b2 * observedGap E1 E2

def H22 (E1 E2 b2 : ℚ) : ℚ :=
  E2 - b2 * observedGap E1 E2

def unperturbedGap (E1 E2 b2 : ℚ) : ℚ :=
  H22 E1 E2 b2 - H11 E1 E2 b2

theorem trace_invariant (E1 E2 b2 : ℚ) :
    H11 E1 E2 b2 + H22 E1 E2 b2 = E1 + E2 := by
  unfold H11 H22 observedGap
  ring

theorem unperturbed_gap_eq (E1 E2 b2 : ℚ) :
    unperturbedGap E1 E2 b2 = (1 - 2 * b2) * observedGap E1 E2 := by
  unfold unperturbedGap H11 H22 observedGap
  ring

def b2FromGap (gap obsGap : ℚ) : ℚ :=
  (1 - gap / obsGap) / 2

theorem b2_from_gap_reconstructs
    (gap obsGap : ℚ) (h : obsGap ≠ 0) :
    (1 - 2 * b2FromGap gap obsGap) * obsGap = gap := by
  unfold b2FromGap
  field_simp [h]
  ring

theorem b2_shift_lower (E1 E2 b2 : ℚ) (h : observedGap E1 E2 ≠ 0) :
    (H11 E1 E2 b2 - E1) / observedGap E1 E2 = b2 := by
  unfold H11
  field_simp [h]
  ring

theorem b2_shift_upper (E1 E2 b2 : ℚ) (h : observedGap E1 E2 ≠ 0) :
    (E2 - H22 E1 E2 b2) / observedGap E1 E2 = b2 := by
  unfold H22
  field_simp [h]
  ring

def H12sq (E1 E2 b2 : ℚ) : ℚ :=
  (b2 - b2 ^ 2) * observedGap E1 E2 ^ 2

theorem H12sq_zero_at_unmixed (E1 E2 : ℚ) :
    H12sq E1 E2 0 = 0 := by
  simp [H12sq]

theorem H12sq_symmetric_half (E1 E2 : ℚ) :
    H12sq E1 E2 (1 / 2) = observedGap E1 E2 ^ 2 / 4 := by
  unfold H12sq
  ring

def symmetricEnergyShift (obsGap gap : ℚ) : ℚ :=
  (obsGap - gap) / 2

theorem symmetric_shift_from_b2 (E1 E2 b2 : ℚ) :
    symmetricEnergyShift (observedGap E1 E2) (unperturbedGap E1 E2 b2) =
      b2 * observedGap E1 E2 := by
  unfold symmetricEnergyShift unperturbedGap H11 H22 observedGap
  ring

def levelRepulsion (b2 : ℚ) : ℚ :=
  b2 / (1 - 2 * b2)

def deltaBar (shellGap traceDefect n : ℚ) : ℚ :=
  shellGap + n * |traceDefect|

def Ebar1 (traceEx delta : ℚ) : ℚ :=
  (traceEx - delta) / 2

def Ebar2 (traceEx delta : ℚ) : ℚ :=
  (traceEx + delta) / 2

theorem Ebar_trace (traceEx delta : ℚ) :
    Ebar1 traceEx delta + Ebar2 traceEx delta = traceEx := by
  unfold Ebar1 Ebar2
  ring

theorem Ebar_gap (traceEx delta : ℚ) :
    Ebar2 traceEx delta - Ebar1 traceEx delta = delta := by
  unfold Ebar1 Ebar2
  ring

def semiEmpiricalB2 (shellGap obsGap traceDefect n : ℚ) : ℚ :=
  ((1 - shellGap / obsGap) - n * |traceDefect| / obsGap) / 2

theorem semiEmpiricalB2_eq_gap_form
    (shellGap obsGap traceDefect n : ℚ) :
    semiEmpiricalB2 shellGap obsGap traceDefect n =
      b2FromGap (deltaBar shellGap traceDefect n) obsGap := by
  unfold semiEmpiricalB2 b2FromGap deltaBar
  ring

def ME1Theory (bi2 bf2 biAbs bfAbs m1 m2 : ℚ) : ℚ :=
  - (1 - bf2) * biAbs * m2 - (1 - bi2) * bfAbs * m1

def MGTTheory (bf2 bfAbs m1 m2 : ℚ) : ℚ :=
  (1 - bf2) * m1 - bfAbs * m2

def Mg24_E1 : ℚ := 982811 / 100
def Mg24_E2 : ℚ := 996719 / 100
def Mg24_shellGap : ℚ := 3
def Mg24_obsGap : ℚ := observedGap Mg24_E1 Mg24_E2
def Mg24_b2_gap : ℚ := b2FromGap Mg24_shellGap Mg24_obsGap

theorem Mg24_observed_gap_exact :
    Mg24_obsGap = 3477 / 25 := by
  norm_num [Mg24_obsGap, observedGap, Mg24_E1, Mg24_E2]

theorem Mg24_gap_formula_b2_exact :
    Mg24_b2_gap = 567 / 1159 := by
  norm_num [Mg24_b2_gap, b2FromGap, Mg24_shellGap, Mg24_obsGap,
    observedGap, Mg24_E1, Mg24_E2]

theorem Mg24_gap_formula_b2_percent_window :
    48 / 100 < Mg24_b2_gap ∧ Mg24_b2_gap < 49 / 100 := by
  norm_num [Mg24_b2_gap, b2FromGap, Mg24_shellGap, Mg24_obsGap,
    observedGap, Mg24_E1, Mg24_E2]

theorem Mg24_unperturbed_gap_reconstructs :
    unperturbedGap Mg24_E1 Mg24_E2 Mg24_b2_gap = Mg24_shellGap := by
  norm_num [unperturbedGap, H11, H22, Mg24_b2_gap, b2FromGap,
    Mg24_shellGap, Mg24_obsGap, observedGap, Mg24_E1, Mg24_E2]

def Mg24_b2_eff_fit : ℚ := 3957 / 10000
def Mg24_b2_free_fit : ℚ := 2755 / 10000

theorem Mg24_effective_fit_percent_window :
    31 / 100 < Mg24_b2_eff_fit ∧ Mg24_b2_eff_fit < 49 / 100 := by
  norm_num [Mg24_b2_eff_fit]

theorem Mg24_free_fit_percent_window :
    31 / 100 < Mg24_b2_free_fit + 607 / 10000 ∧
      Mg24_b2_free_fit + 607 / 10000 < 49 / 100 := by
  norm_num [Mg24_b2_free_fit]

def Co54_E1 : ℚ := 265198 / 100
def Co54_E2 : ℚ := 285130 / 100
def Co54_H11_central : ℚ := 265244 / 100
def Co54_H22_central : ℚ := 285084 / 100

theorem Co54_observed_gap_exact :
    observedGap Co54_E1 Co54_E2 = 4983 / 25 := by
  norm_num [observedGap, Co54_E1, Co54_E2]

theorem Co54_table_unperturbed_gap_exact :
    Co54_H22_central - Co54_H11_central = 992 / 5 := by
  norm_num [Co54_H11_central, Co54_H22_central]

def P30_bi2_percent : ℚ := 4723 / 1000
def S32_bf2_percent : ℚ := 2688 / 1000
def Cl34_bi2_percent : ℚ := 237 / 1000
def Ar36_bf2_percent : ℚ := 2460 / 1000

theorem tableI_selected_percent_values :
    P30_bi2_percent = 4723 / 1000 ∧
      S32_bf2_percent = 336 / 125 ∧
      Cl34_bi2_percent = 237 / 1000 ∧
      Ar36_bf2_percent = 123 / 50 := by
  norm_num [P30_bi2_percent, S32_bf2_percent, Cl34_bi2_percent,
    Ar36_bf2_percent]

def formalSummary : Prop :=
    Mg24_obsGap = 3477 / 25 ∧
    Mg24_b2_gap = 567 / 1159 ∧
    unperturbedGap Mg24_E1 Mg24_E2 Mg24_b2_gap = Mg24_shellGap ∧
    Co54_H22_central - Co54_H11_central = 992 / 5 ∧
    P30_bi2_percent = 4723 / 1000

theorem formalSummary_proved : formalSummary := by
  exact ⟨Mg24_observed_gap_exact, Mg24_gap_formula_b2_exact,
    Mg24_unperturbed_gap_reconstructs, Co54_table_unperturbed_gap_exact, rfl⟩

end SarkarTwoLevelIsospinMixing

end noncomputable section
