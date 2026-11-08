import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace CakirliPnInteractionIsospin

def Tz (N Z : ℚ) : ℚ :=
  (N - Z) / 2

theorem Tz_mirror_negates (Z N : ℚ) :
    Tz Z N = -Tz N Z := by
  unfold Tz
  ring

theorem Tz_A23_Na_Mg :
    Tz 12 11 = 1 / 2 ∧ Tz 11 12 = -1 / 2 := by
  norm_num [Tz]

def bindingEnergy (Z N mp mn M c2 : ℚ) : ℚ :=
  (Z * mp + N * mn - M) * c2

theorem bindingEnergy_mass_reconstruction
    (Z N mp mn M c2 : ℚ) (hc : c2 ≠ 0) :
    M = Z * mp + N * mn - bindingEnergy Z N mp mn M c2 / c2 := by
  unfold bindingEnergy
  field_simp [hc]
  ring

def deltaVpn_oe (B : ℤ → ℤ → ℚ) (Z N : ℤ) : ℚ :=
  ((B Z N - B Z (N - 2)) - (B (Z - 1) N - B (Z - 1) (N - 2))) / 2

def deltaVpn_eo (B : ℤ → ℤ → ℚ) (Z N : ℤ) : ℚ :=
  ((B Z N - B Z (N - 1)) - (B (Z - 2) N - B (Z - 2) (N - 1))) / 2

theorem deltaVpn_oe_affine_binding_zero
    (a b c : ℚ) (Z N : ℤ) :
    deltaVpn_oe (fun Z N => a * Z + b * N + c) Z N = 0 := by
  unfold deltaVpn_oe
  ring

theorem deltaVpn_eo_affine_binding_zero
    (a b c : ℚ) (Z N : ℤ) :
    deltaVpn_eo (fun Z N => a * Z + b * N + c) Z N = 0 := by
  unfold deltaVpn_eo
  ring

def mirrorDelta (delta_Tz_neg_half delta_Tz_pos_half : ℚ) : ℚ :=
  delta_Tz_neg_half - delta_Tz_pos_half

theorem mirrorDelta_antisym (x y : ℚ) :
    mirrorDelta x y = -mirrorDelta y x := by
  unfold mirrorDelta
  ring

structure MirrorDeltaDatum where
  A : ℕ
  tzPosNucleus : String
  tzNegNucleus : String
  deltaTzPosHalf_keV : ℚ
  deltaTzNegHalf_keV : ℚ
  reportedDelta_keV : ℚ
  reportedError_keV : ℚ

def centralDelta (d : MirrorDeltaDatum) : ℚ :=
  mirrorDelta d.deltaTzNegHalf_keV d.deltaTzPosHalf_keV

def withinReportedError (d : MirrorDeltaDatum) : Prop :=
  |centralDelta d - d.reportedDelta_keV| ≤ d.reportedError_keV

def A7_Li_Be : MirrorDeltaDatum where
  A := 7
  tzPosNucleus := "7Li"
  tzNegNucleus := "7Be"
  deltaTzPosHalf_keV := 5970
  deltaTzNegHalf_keV := 5785
  reportedDelta_keV := -185
  reportedError_keV := 35

def A9_Be_B : MirrorDeltaDatum where
  A := 9
  tzPosNucleus := "9Be"
  tzNegNucleus := "9B"
  deltaTzPosHalf_keV := 1037
  deltaTzNegHalf_keV := 914
  reportedDelta_keV := -123
  reportedError_keV := 13

def A13_C_N : MirrorDeltaDatum where
  A := 13
  tzPosNucleus := "13C"
  tzNegNucleus := "13N"
  deltaTzPosHalf_keV := 2222
  deltaTzNegHalf_keV := 1661
  reportedDelta_keV := -562
  reportedError_keV := 3

def A15_N_O : MirrorDeltaDatum where
  A := 15
  tzPosNucleus := "15N"
  tzNegNucleus := "15O"
  deltaTzPosHalf_keV := 41320 / 10
  deltaTzNegHalf_keV := 41384 / 10
  reportedDelta_keV := 64 / 10
  reportedError_keV := 1 / 10

def A17_O_F : MirrorDeltaDatum where
  A := 17
  tzPosNucleus := "17O"
  tzNegNucleus := "17F"
  deltaTzPosHalf_keV := 14625 / 10
  deltaTzNegHalf_keV := 935
  reportedDelta_keV := -527
  reportedError_keV := 7

def A19_F_Ne : MirrorDeltaDatum where
  A := 19
  tzPosNucleus := "19F"
  tzNegNucleus := "19Ne"
  deltaTzPosHalf_keV := 36966 / 10
  deltaTzNegHalf_keV := 37467 / 10
  reportedDelta_keV := 500 / 10
  reportedError_keV := 3 / 10

def A23_Na_Mg : MirrorDeltaDatum where
  A := 23
  tzPosNucleus := "23Na"
  tzNegNucleus := "23Mg"
  deltaTzPosHalf_keV := 318140 / 100
  deltaTzNegHalf_keV := 31920 / 10
  reportedDelta_keV := 106 / 10
  reportedError_keV := 1 / 10

def A25_Mg_Al : MirrorDeltaDatum where
  A := 25
  tzPosNucleus := "25Mg"
  tzNegNucleus := "25Al"
  deltaTzPosHalf_keV := 10650 / 10
  deltaTzNegHalf_keV := 10650 / 10
  reportedDelta_keV := 3 / 10
  reportedError_keV := 3 / 10

def A29_Si_P : MirrorDeltaDatum where
  A := 29
  tzPosNucleus := "29Si"
  tzNegNucleus := "29P"
  deltaTzPosHalf_keV := 101510 / 100
  deltaTzNegHalf_keV := 971
  reportedDelta_keV := -44
  reportedError_keV := 5

theorem A7_delta_exact : centralDelta A7_Li_Be = -185 := by
  norm_num [centralDelta, mirrorDelta, A7_Li_Be]

theorem A9_delta_exact : centralDelta A9_Be_B = -123 := by
  norm_num [centralDelta, mirrorDelta, A9_Be_B]

theorem A13_delta_within_error : withinReportedError A13_C_N := by
  norm_num [withinReportedError, centralDelta, mirrorDelta, A13_C_N]

theorem A15_delta_exact : centralDelta A15_N_O = 64 / 10 := by
  norm_num [centralDelta, mirrorDelta, A15_N_O]

theorem A17_delta_within_error : withinReportedError A17_O_F := by
  norm_num [withinReportedError, centralDelta, mirrorDelta, A17_O_F]

theorem A19_delta_within_error : withinReportedError A19_F_Ne := by
  norm_num [withinReportedError, centralDelta, mirrorDelta, A19_F_Ne]

theorem A23_delta_exact : centralDelta A23_Na_Mg = 106 / 10 := by
  norm_num [centralDelta, mirrorDelta, A23_Na_Mg]

theorem A25_delta_near_zero : withinReportedError A25_Mg_Al := by
  norm_num [withinReportedError, centralDelta, mirrorDelta, A25_Mg_Al]

theorem A29_delta_within_error : withinReportedError A29_Si_P := by
  norm_num [withinReportedError, centralDelta, mirrorDelta, A29_Si_P]

def nearZeroBand (x : ℚ) : Prop :=
  |x| ≤ 50

theorem A25_in_50keV_band : nearZeroBand (centralDelta A25_Mg_Al) := by
  norm_num [nearZeroBand, centralDelta, mirrorDelta, A25_Mg_Al]

theorem A13_outside_50keV_band : ¬ nearZeroBand (centralDelta A13_C_N) := by
  norm_num [nearZeroBand, centralDelta, mirrorDelta, A13_C_N]

theorem A17_outside_50keV_band : ¬ nearZeroBand (centralDelta A17_O_F) := by
  norm_num [nearZeroBand, centralDelta, mirrorDelta, A17_O_F]

def largeBarMass (A : ℕ) : Prop :=
  A % 4 = 3

def smallBarMass (A : ℕ) : Prop :=
  A % 4 = 1

theorem A7_A11_A15_A19_large_bar :
    largeBarMass 7 ∧ largeBarMass 11 ∧ largeBarMass 15 ∧ largeBarMass 19 := by
  norm_num [largeBarMass]

theorem A9_A13_A17_A21_small_bar :
    smallBarMass 9 ∧ smallBarMass 13 ∧ smallBarMass 17 ∧ smallBarMass 21 := by
  norm_num [smallBarMass]

def formalSummary : Prop :=
  Tz 12 11 = 1 / 2 ∧
    Tz 11 12 = -1 / 2 ∧
    centralDelta A7_Li_Be = -185 ∧
    centralDelta A9_Be_B = -123 ∧
    withinReportedError A13_C_N ∧
    nearZeroBand (centralDelta A25_Mg_Al) ∧
    ¬ nearZeroBand (centralDelta A17_O_F)

theorem formalSummary_proved : formalSummary := by
  exact ⟨Tz_A23_Na_Mg.1, Tz_A23_Na_Mg.2, A7_delta_exact,
    A9_delta_exact, A13_delta_within_error, A25_in_50keV_band,
    A17_outside_50keV_band⟩

end CakirliPnInteractionIsospin

end noncomputable section
