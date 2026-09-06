import Mathlib

noncomputable section

namespace LlewellynZr79MED

def Tz (N Z : ℚ) : ℚ :=
  (N - Z) / 2

theorem Zr79_Y79_Tz :
    Tz 39 40 = -1 / 2 ∧ Tz 40 39 = 1 / 2 := by
  norm_num [Tz]

def MED (excitation_Tz_neg_half excitation_Tz_pos_half : ℚ) : ℚ :=
  excitation_Tz_neg_half - excitation_Tz_pos_half

theorem MED_antisym (x y : ℚ) : MED x y = -MED y x := by
  unfold MED
  ring

def levelFromTransition (lower gamma : ℚ) : ℚ :=
  lower + gamma

def withinError (central reported error : ℚ) : Prop :=
  |central - reported| ≤ error

structure MirrorBandState where
  twoJ : ℕ
  Ezr_keV : ℚ
  Ey_keV : ℚ
  Eth_zr_keV : ℚ
  Eth_y_keV : ℚ
  med_keV : ℚ
  med_error_keV : ℚ

def state7_2 : MirrorBandState where
  twoJ := 7
  Ezr_keV := 184
  Ey_keV := 183
  Eth_zr_keV := 228
  Eth_y_keV := 226
  med_keV := 1
  med_error_keV := 1

def state9_2 : MirrorBandState where
  twoJ := 9
  Ezr_keV := 416
  Ey_keV := 411
  Eth_zr_keV := 522
  Eth_y_keV := 515
  med_keV := 5
  med_error_keV := 2

def state11_2 : MirrorBandState where
  twoJ := 11
  Ezr_keV := 715
  Ey_keV := 726
  Eth_zr_keV := 886
  Eth_y_keV := 875
  med_keV := -11
  med_error_keV := 4

def state13_2 : MirrorBandState where
  twoJ := 13
  Ezr_keV := 1042
  Ey_keV := 1042
  Eth_zr_keV := 1291
  Eth_y_keV := 1291
  med_keV := 0
  med_error_keV := 1

def centralMED (s : MirrorBandState) : ℚ :=
  MED s.Ezr_keV s.Ey_keV

def reportedMEDConsistent (s : MirrorBandState) : Prop :=
  withinError (centralMED s) s.med_keV s.med_error_keV

theorem state7_2_MED_exact :
    centralMED state7_2 = 1 := by
  norm_num [centralMED, MED, state7_2]

theorem state9_2_MED_exact :
    centralMED state9_2 = 5 := by
  norm_num [centralMED, MED, state9_2]

theorem state11_2_MED_exact :
    centralMED state11_2 = -11 := by
  norm_num [centralMED, MED, state11_2]

theorem state13_2_MED_exact :
    centralMED state13_2 = 0 := by
  norm_num [centralMED, MED, state13_2]

theorem reported_MED_all_consistent :
    reportedMEDConsistent state7_2 ∧
      reportedMEDConsistent state9_2 ∧
      reportedMEDConsistent state11_2 ∧
      reportedMEDConsistent state13_2 := by
  norm_num [reportedMEDConsistent, withinError, centralMED, MED,
    state7_2, state9_2, state11_2, state13_2]

def betaY184 : ℚ := 294 / 1000
def betaY227_411 : ℚ := 296 / 1000
def betaYHigh : ℚ := 304 / 1000
def betaZr184 : ℚ := 298 / 1000
def betaZrHigh : ℚ := 304 / 1000

theorem beta_ordering :
    betaY184 < betaY227_411 ∧ betaY227_411 < betaYHigh ∧
      betaZr184 < betaZrHigh := by
  norm_num [betaY184, betaY227_411, betaYHigh, betaZr184, betaZrHigh]

theorem Y79_cascade_cross_over_discrepancy :
    levelFromTransition 183 227 - 411 = -1 := by
  norm_num [levelFromTransition]

theorem Zr79_cascade_cross_over_discrepancy :
    levelFromTransition 184 230 - 416 = -2 := by
  norm_num [levelFromTransition]

theorem Y79_cascade_within_three_keV :
    |levelFromTransition 183 227 - 411| ≤ 3 := by
  norm_num [levelFromTransition]

theorem Zr79_cascade_within_three_keV :
    |levelFromTransition 184 230 - 416| ≤ 3 := by
  norm_num [levelFromTransition]

def ncciResidual (experimentalMED theoreticalMED : ℚ) : ℚ :=
  experimentalMED - theoreticalMED

theorem NCCI_first_two_MED_residuals_small :
    |ncciResidual (centralMED state7_2)
        (state7_2.Eth_zr_keV - state7_2.Eth_y_keV)| ≤ 2 ∧
      |ncciResidual (centralMED state9_2)
        (state9_2.Eth_zr_keV - state9_2.Eth_y_keV)| ≤ 2 := by
  norm_num [ncciResidual, centralMED, MED, state7_2, state9_2]

def configurationCount_selected : ℕ := 40
def configurationCount_mixing : ℕ := 10

theorem selected_to_mixing_configurations :
    configurationCount_mixing * 4 = configurationCount_selected := by
  norm_num [configurationCount_selected, configurationCount_mixing]

def formalSummary : Prop :=
  Tz 39 40 = -1 / 2 ∧
    Tz 40 39 = 1 / 2 ∧
    centralMED state7_2 = 1 ∧
    centralMED state9_2 = 5 ∧
    centralMED state11_2 = -11 ∧
    betaY184 < betaYHigh ∧
    |levelFromTransition 184 230 - 416| ≤ 3

theorem formalSummary_proved : formalSummary := by
  exact ⟨Zr79_Y79_Tz.1, Zr79_Y79_Tz.2, state7_2_MED_exact,
    state9_2_MED_exact, state11_2_MED_exact, beta_ordering.1.trans beta_ordering.2.1,
    Zr79_cascade_within_three_keV⟩

end LlewellynZr79MED

end noncomputable section
