import Mathlib

/-!
# B(M1) Mirror Ratios in a Finite TKK-Style Model

This module records a small real-valued model for mirror-nucleus B(M1) ratios.
The formal content is intentionally finite: definitions are explicit arithmetic
expressions, and the theorems prove algebraic consequences of those expressions.
-/

noncomputable section

namespace BM1MirrorNuclei

/-!
## Section 1: M1 Operator Data
-/

/--
M1 transition operator in the shell-model notation used by the surrounding
notes.
-/
def M1_operator : String := "sqrt(3/4*pi) * (g_l^IV * L + g_s^IV * S)"

/--
Isovector M1 operator as a spin-isospin tensor.
-/
def M1_isovector : String := "sigma tau_0"

/--
The two Clebsch-Gordan signs for the mirror pair have the same square.
-/
theorem GT_M1_isospin_relation :
    let CG_plus := (1 : ℝ) / Real.sqrt 2
    let CG_minus := -(1 : ℝ) / Real.sqrt 2
    CG_plus ^ 2 = CG_minus ^ 2 := by
  ring

/-!
## Section 2: B(M1) Ratio Formula
-/

/--
Mass-number dependence for the finite B(M1) mirror-ratio model.

The expression keeps the triality ratio `17/11`, a smaller M1 surface term
`3 / (10 * A)`, and a linear coupling factor `1 + chi_M1 / 100`.  This avoids
unproved real-exponential numerics while retaining an explicit mass and coupling
dependence.
-/
def BM1_ratio_prediction (A : ℝ) (chi_M1 : ℝ) : ℝ :=
  ((17 : ℝ) / 11) * (1 + ((3 : ℝ) / 10) / A) * (1 + chi_M1 / 100)

/--
Default M1 triality coupling used by this file.
-/
def default_chi_M1 : ℝ := 50

/--
The A = 27 prediction is a direct rational unfolding of the finite model.
-/
theorem BM1_ratio_A27_prediction :
    BM1_ratio_prediction 27 default_chi_M1 = (1547 : ℝ) / 660 := by
  norm_num [BM1_ratio_prediction, default_chi_M1]

/--
The A = 43 prediction is a direct rational unfolding of the finite model.
-/
theorem BM1_ratio_A43_prediction :
    BM1_ratio_prediction 43 default_chi_M1 = (22083 : ℝ) / 9460 := by
  norm_num [BM1_ratio_prediction, default_chi_M1]

/--
The A = 31 prediction is a direct rational unfolding of the finite model.
-/
theorem BM1_ratio_A31_prediction :
    BM1_ratio_prediction 31 default_chi_M1 = (15963 : ℝ) / 6820 := by
  norm_num [BM1_ratio_prediction, default_chi_M1]

/-!
## Section 3: Mass Dependence
-/

/--
The finite model decreases with mass number for positive masses.
-/
theorem BM1_mass_dependence_monotonic :
    ∀ (A1 A2 : ℝ), 0 < A1 → A1 < A2 →
      BM1_ratio_prediction A1 default_chi_M1 >
        BM1_ratio_prediction A2 default_chi_M1 := by
  intro A1 A2 hA1_pos hA1_lt_A2
  have hrec : (1 / A2 : ℝ) < 1 / A1 := by
    apply one_div_lt_one_div_of_lt hA1_pos hA1_lt_A2
  have hdiv : ((3 : ℝ) / 10) / A2 < ((3 : ℝ) / 10) / A1 := by
    have hscaled : ((3 : ℝ) / 10) * (1 / A2) <
        ((3 : ℝ) / 10) * (1 / A1) := by
      apply mul_lt_mul_of_pos_left hrec
      norm_num
    simpa [div_eq_mul_inv] using hscaled
  have hsurf : (1 + ((3 : ℝ) / 10) / A2) <
      (1 + ((3 : ℝ) / 10) / A1) := by
    linarith
  unfold BM1_ratio_prediction default_chi_M1
  norm_num
  linarith

/--
Specific mass ordering for the listed nuclei.
-/
theorem BM1_mass_ordering :
    BM1_ratio_prediction 27 default_chi_M1 > BM1_ratio_prediction 31 default_chi_M1 ∧
    BM1_ratio_prediction 31 default_chi_M1 > BM1_ratio_prediction 35 default_chi_M1 ∧
    BM1_ratio_prediction 35 default_chi_M1 > BM1_ratio_prediction 39 default_chi_M1 ∧
    BM1_ratio_prediction 39 default_chi_M1 > BM1_ratio_prediction 43 default_chi_M1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact BM1_mass_dependence_monotonic 27 31 (by norm_num) (by norm_num)
  · exact BM1_mass_dependence_monotonic 31 35 (by norm_num) (by norm_num)
  · exact BM1_mass_dependence_monotonic 35 39 (by norm_num) (by norm_num)
  · exact BM1_mass_dependence_monotonic 39 43 (by norm_num) (by norm_num)

/-!
## Section 4: Shell Corrections
-/

/--
Shell correction factors for selected B(M1) mirror ratios.
-/
def BM1_shell_corrections : List (ℝ × String) :=
  [(27, "mid-shell enhancement: x1.20"),
   (31, "near-magic: x1.00"),
   (35, "near-magic: x1.05"),
   (39, "near-magic: x1.00"),
   (43, "approaching N=28: x0.90")]

/--
Shell-corrected B(M1) ratio for selected nuclei.
-/
def BM1_ratio_with_shell_correction (A : ℝ) : ℝ :=
  let base := BM1_ratio_prediction A default_chi_M1
  if A = 27 then
    base * (6 / 5)
  else if A = 35 then
    base * (21 / 20)
  else if A = 43 then
    base * (9 / 10)
  else
    base

/--
The selected shell factors raise A = 27, lower A = 43, and leave A = 31 and
A = 39 unchanged.
-/
theorem BM1_shell_corrected_pattern :
    BM1_ratio_with_shell_correction 27 > BM1_ratio_prediction 27 default_chi_M1 ∧
    BM1_ratio_with_shell_correction 43 < BM1_ratio_prediction 43 default_chi_M1 ∧
    BM1_ratio_with_shell_correction 31 = BM1_ratio_prediction 31 default_chi_M1 ∧
    BM1_ratio_with_shell_correction 39 = BM1_ratio_prediction 39 default_chi_M1 := by
  have h27_pos : 0 < BM1_ratio_prediction 27 default_chi_M1 := by
    norm_num [BM1_ratio_prediction, default_chi_M1]
  have h43_pos : 0 < BM1_ratio_prediction 43 default_chi_M1 := by
    norm_num [BM1_ratio_prediction, default_chi_M1]
  constructor
  · simp [BM1_ratio_with_shell_correction]
    nlinarith
  constructor
  · simp [BM1_ratio_with_shell_correction]
    nlinarith
  constructor
  · simp [BM1_ratio_with_shell_correction]
  · simp [BM1_ratio_with_shell_correction]

/-!
## Section 5: Coupling Ratio
-/

/--
Ratio of M1 to E1 triality couplings.
-/
def chi_ratio : ℝ := default_chi_M1 / 75

/-- The coupling ratio is exactly two thirds in this finite model. -/
theorem chi_ratio_value :
    chi_ratio = 2 / 3 := by
  norm_num [chi_ratio, default_chi_M1]

/--
The ratio statement fixes the same default coupling used in the definitions.
-/
theorem chi_ratio_physical_meaning :
    chi_ratio = 2 / 3 →
      default_chi_M1 / 75 = (2 : ℝ) / 3 := by
  intro h
  simpa [chi_ratio] using h

/-!
## Section 6: Experimental Comparison
-/

/--
No direct A = 27 mirror-ratio measurement is recorded in this finite file.
-/
def BM1_ratio_A27_exp : Option ℝ := none

/--
Relative absolute discrepancy from the shell-corrected A = 27 prediction.
-/
def BM1_A27_discrepancy (exp_val : ℝ) : ℝ :=
  |BM1_ratio_with_shell_correction 27 - exp_val| / exp_val

/--
The finite A = 27 comparison reduces any recorded positive value to the named
relative discrepancy formula.
-/
theorem BM1_A27_comparison (exp_val : ℝ) (h_exp_pos : exp_val > 0) :
    BM1_ratio_A27_exp = some exp_val →
      0 ≤ BM1_A27_discrepancy exp_val ∧
      BM1_A27_discrepancy exp_val =
        |((1547 : ℝ) / 550) - exp_val| / exp_val := by
  intro _h_recorded
  constructor
  · unfold BM1_A27_discrepancy
    apply div_nonneg
    · apply abs_nonneg
    · linarith
  · unfold BM1_A27_discrepancy
    norm_num [BM1_ratio_with_shell_correction, BM1_ratio_prediction,
      default_chi_M1]

/-!
## Section 7: Summary
-/

/--
Main finite summary: selected shell-corrected values, the coupling ratio, and
the mass-dependence theorem all follow from the definitions above.
-/
theorem BM1_TKK_framework_summary :
    (BM1_ratio_with_shell_correction 27 = (1547 : ℝ) / 550) ∧
    (BM1_ratio_with_shell_correction 31 = (15963 : ℝ) / 6820) ∧
    (BM1_ratio_with_shell_correction 43 = (198747 : ℝ) / 94600) ∧
    (chi_ratio = 2 / 3) ∧
    (BM1_ratio_prediction 27 default_chi_M1 >
      BM1_ratio_prediction 43 default_chi_M1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [BM1_ratio_with_shell_correction, BM1_ratio_prediction, default_chi_M1]
  · norm_num [BM1_ratio_with_shell_correction, BM1_ratio_prediction, default_chi_M1]
  · norm_num [BM1_ratio_with_shell_correction, BM1_ratio_prediction, default_chi_M1]
  · exact chi_ratio_value
  · exact BM1_mass_dependence_monotonic 27 43 (by norm_num) (by norm_num)

end BM1MirrorNuclei

end noncomputable section
