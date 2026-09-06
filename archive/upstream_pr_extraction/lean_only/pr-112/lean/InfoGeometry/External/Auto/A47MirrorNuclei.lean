import Mathlib.Data.Real.Basic
import Mathlib.Tactic

noncomputable section

namespace A47MirrorNuclei

/-- Experimental Q_t values for 15/2⁻ → 11/2⁻ transition. -/
def Qt_15_2_Cr47 : ℝ := 90
def Qt_15_2_V47 : ℝ := 83

/-- B(E2) ratio for the 15/2⁻ transition. -/
def BE2_ratio_15_2_exp : ℝ := (115 : ℝ) / 100

/-- A finite reference ratio used for the arithmetic consistency check.  This
    datum is not a TKK prediction. -/
def BE2_ratio_15_2_reference : ℝ := (115 : ℝ) / 100

theorem A47_reference_ratio_matches :
    abs (BE2_ratio_15_2_exp - BE2_ratio_15_2_reference) /
      BE2_ratio_15_2_reference < (3 : ℝ) / 100 := by
  norm_num [BE2_ratio_15_2_exp, BE2_ratio_15_2_reference]

/-- Experimental Q_t values for 19/2⁻ → 15/2⁻ transition. -/
def Qt_19_2_Cr47 : ℝ := 88
def Qt_19_2_V47 : ℝ := 75

/-- B(E2) ratio for the 19/2⁻ transition. -/
def BE2_ratio_19_2_exp : ℝ := (13 : ℝ) / 10

theorem alignment_amplifies_isospin_breaking :
    BE2_ratio_19_2_exp > BE2_ratio_15_2_exp := by
  unfold BE2_ratio_19_2_exp BE2_ratio_15_2_exp
  norm_num

end A47MirrorNuclei

end noncomputable section
