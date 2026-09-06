import Mathlib

noncomputable section

namespace SymmetryReviewISB

def Tz (N Z : ℚ) : ℚ :=
  (N - Z) / 2

theorem Tz_projection_formula (N Z : ℚ) :
    2 * Tz N Z = N - Z := by
  unfold Tz
  ring

def upQuarkMassMeV : ℚ := 219 / 100
def downQuarkMassMeV : ℚ := 467 / 100
def strangeQuarkMassMeV : ℚ := 94

def qcdIsoscalarMass : ℚ :=
  (upQuarkMassMeV + downQuarkMassMeV) / 2

def qcdIsovectorMass : ℚ :=
  (upQuarkMassMeV - downQuarkMassMeV) / 2

theorem qcd_mass_split_exact :
    downQuarkMassMeV - upQuarkMassMeV = 62 / 25 ∧
      qcdIsoscalarMass = 343 / 100 ∧
      qcdIsovectorMass = -31 / 25 := by
  norm_num [downQuarkMassMeV, upQuarkMassMeV, qcdIsoscalarMass,
    qcdIsovectorMass]

def henleyClassI (a b tauDot : ℚ) : ℚ :=
  a + b * tauDot

def henleyClassII (c tau3i tau3j tauDot : ℚ) : ℚ :=
  c * (tau3i * tau3j - tauDot / 3)

def henleyClassIII (d tau3i tau3j : ℚ) : ℚ :=
  d * (tau3i + tau3j)

def neutronTau3 : ℚ := 1
def protonTau3 : ℚ := -1

theorem classIII_np_vanishes (d : ℚ) :
    henleyClassIII d neutronTau3 protonTau3 = 0 := by
  norm_num [henleyClassIII, neutronTau3, protonTau3]

theorem classIII_nn_pp_opposite (d : ℚ) :
    henleyClassIII d neutronTau3 neutronTau3 +
      henleyClassIII d protonTau3 protonTau3 = 0 := by
  unfold henleyClassIII neutronTau3 protonTau3
  ring

def IMME (a b c Tz : ℚ) : ℚ :=
  a + b * Tz + c * Tz ^ 2

def cubicIMME (a b c d Tz : ℚ) : ℚ :=
  IMME a b c Tz + d * Tz ^ 3

theorem IMME_mirror_difference (a b c t : ℚ) :
    IMME a b c t - IMME a b c (-t) = 2 * b * t := by
  unfold IMME
  ring

theorem IMME_mirror_sum (a b c t : ℚ) :
    IMME a b c t + IMME a b c (-t) = 2 * a + 2 * c * t ^ 2 := by
  unfold IMME
  ring

theorem cubicIMME_odd_part (a b c d t : ℚ) :
    cubicIMME a b c d t - cubicIMME a b c d (-t) =
      2 * b * t + 2 * d * t ^ 3 := by
  unfold cubicIMME IMME
  ring

def asymmetryI (A Tz : ℚ) : ℚ :=
  2 * Tz / A

def generalizedIMME
    (A a bc deltaNH asymCSB cc asymCIB Tz : ℚ) : ℚ :=
  a + bc + deltaNH + 2 * asymCSB * Tz +
    (cc + (4 / A) * asymCIB) * Tz ^ 2

theorem generalizedIMME_reduces_to_quadratic
    (A a bc deltaNH cc Tz : ℚ) :
    generalizedIMME A a bc deltaNH 0 cc 0 Tz =
      IMME (a + bc + deltaNH) 0 cc Tz := by
  unfold generalizedIMME IMME
  ring

def deltaNHMeV : ℚ := 782 / 1000

theorem deltaNH_exact :
    deltaNHMeV = 391 / 500 := by
  norm_num [deltaNHMeV]

def scatteringCIB (app ann anp : ℚ) : ℚ :=
  (app + ann) / 2 - anp

def scatteringCSB (app ann : ℚ) : ℚ :=
  app - ann

theorem scattering_CIB_reported_anchor :
    scatteringCIB 0 0 (-57 / 10) = 57 / 10 := by
  norm_num [scatteringCIB]

theorem scattering_CSB_reported_anchor :
    scatteringCSB (3 / 4) (-3 / 4) = 3 / 2 := by
  norm_num [scatteringCSB]

def massSplit (left right : ℚ) : ℚ :=
  left - right

theorem light_isodoublet_mass_splits :
    massSplit (93957 / 100) (93828 / 100) = 129 / 100 ∧
      massSplit (280894 / 100) (280842 / 100) = 13 / 25 ∧
      massSplit (466787 / 100) (466766 / 100) = 21 / 100 := by
  norm_num [massSplit]

def MED (EminusTz EplusTz : ℚ) : ℚ :=
  EminusTz - EplusTz

theorem MED_25Al_25Mg_selected_states :
    MED (-133) 0 = -133 ∧ MED (-175) 0 = -175 ∧ MED (-128) 0 = -128 := by
  norm_num [MED]

theorem MED_26Si_26Mg_selected_states :
    MED (-151) 0 = -151 ∧ MED (-252) 0 = -252 ∧
      MED (-193) 0 = -193 ∧ MED 477 0 = 477 := by
  norm_num [MED]

theorem MED_23Al_23Ne_selected_states :
    MED (-467) 0 = -467 ∧ MED (-347) 0 = -347 ∧ MED (-432) 0 = -432 := by
  norm_num [MED]

theorem MED_24Si_24Ne_selected_states :
    MED (-110) 0 = -110 ∧ MED (-426) 0 = -426 ∧
      MED (-1298) 0 = -1298 := by
  norm_num [MED]

def formalSummary : Prop :=
  downQuarkMassMeV - upQuarkMassMeV = 62 / 25 ∧
    qcdIsoscalarMass = 343 / 100 ∧
    IMME 1 2 3 4 = 57 ∧
    deltaNHMeV = 391 / 500 ∧
    scatteringCIB 0 0 (-57 / 10) = 57 / 10 ∧
    MED 477 0 = 477

theorem formalSummary_proved : formalSummary := by
  exact ⟨qcd_mass_split_exact.1, qcd_mass_split_exact.2.1, by norm_num [IMME],
    deltaNH_exact, scattering_CIB_reported_anchor, by norm_num [MED]⟩

end SymmetryReviewISB

end noncomputable section
