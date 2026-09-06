import Mathlib.Tactic

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

abbrev MirrorBandState := ℕ × ℚ × ℚ × ℚ × ℚ × ℚ × ℚ

namespace MirrorBandState

abbrev twoJ (s : MirrorBandState) : ℕ := s.1

abbrev Ezr_keV (s : MirrorBandState) : ℚ := s.2.1

abbrev Ey_keV (s : MirrorBandState) : ℚ := s.2.2.1

abbrev Eth_zr_keV (s : MirrorBandState) : ℚ := s.2.2.2.1

abbrev Eth_y_keV (s : MirrorBandState) : ℚ := s.2.2.2.2.1

abbrev med_keV (s : MirrorBandState) : ℚ := s.2.2.2.2.2.1

abbrev med_error_keV (s : MirrorBandState) : ℚ := s.2.2.2.2.2.2

end MirrorBandState

def state7_2 : MirrorBandState := (7, 184, 183, 228, 226, 1, 1)

def state9_2 : MirrorBandState := (9, 416, 411, 522, 515, 5, 2)

def state11_2 : MirrorBandState := (11, 715, 726, 886, 875, -11, 4)

def state13_2 : MirrorBandState := (13, 1042, 1042, 1291, 1291, 0, 1)

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

end LlewellynZr79MED

end noncomputable section
