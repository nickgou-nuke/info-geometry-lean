import Mathlib.Tactic

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

abbrev MirrorDeltaDatum :=
  ℕ × String × String × ℚ × ℚ × ℚ × ℚ

namespace MirrorDeltaDatum

def A (d : MirrorDeltaDatum) : ℕ := d.1
def tzPosNucleus (d : MirrorDeltaDatum) : String := d.2.1
def tzNegNucleus (d : MirrorDeltaDatum) : String := d.2.2.1
def deltaTzPosHalf_keV (d : MirrorDeltaDatum) : ℚ := d.2.2.2.1
def deltaTzNegHalf_keV (d : MirrorDeltaDatum) : ℚ := d.2.2.2.2.1
def reportedDelta_keV (d : MirrorDeltaDatum) : ℚ := d.2.2.2.2.2.1
def reportedError_keV (d : MirrorDeltaDatum) : ℚ := d.2.2.2.2.2.2

end MirrorDeltaDatum

def centralDelta (d : MirrorDeltaDatum) : ℚ :=
  mirrorDelta (MirrorDeltaDatum.deltaTzNegHalf_keV d)
    (MirrorDeltaDatum.deltaTzPosHalf_keV d)

def withinReportedError (d : MirrorDeltaDatum) : Prop :=
  |centralDelta d - MirrorDeltaDatum.reportedDelta_keV d| ≤
    MirrorDeltaDatum.reportedError_keV d

def A7_Li_Be : MirrorDeltaDatum :=
  (7, "7Li", "7Be", 5970, 5785, -185, 35)

def A9_Be_B : MirrorDeltaDatum :=
  (9, "9Be", "9B", 1037, 914, -123, 13)

def A13_C_N : MirrorDeltaDatum :=
  (13, "13C", "13N", 2222, 1661, -562, 3)

def A15_N_O : MirrorDeltaDatum :=
  (15, "15N", "15O", 41320 / 10, 41384 / 10, 64 / 10, 1 / 10)

def A17_O_F : MirrorDeltaDatum :=
  (17, "17O", "17F", 14625 / 10, 935, -527, 7)

def A19_F_Ne : MirrorDeltaDatum :=
  (19, "19F", "19Ne", 36966 / 10, 37467 / 10, 500 / 10, 3 / 10)

def A23_Na_Mg : MirrorDeltaDatum :=
  (23, "23Na", "23Mg", 318140 / 100, 31920 / 10, 106 / 10, 1 / 10)

def A25_Mg_Al : MirrorDeltaDatum :=
  (25, "25Mg", "25Al", 10650 / 10, 10650 / 10, 3 / 10, 3 / 10)

def A29_Si_P : MirrorDeltaDatum :=
  (29, "29Si", "29P", 101510 / 100, 971, -44, 5)

theorem A7_delta_exact : centralDelta A7_Li_Be = -185 := by
  norm_num [centralDelta, mirrorDelta, MirrorDeltaDatum.deltaTzNegHalf_keV,
    MirrorDeltaDatum.deltaTzPosHalf_keV, A7_Li_Be]

theorem A9_delta_exact : centralDelta A9_Be_B = -123 := by
  norm_num [centralDelta, mirrorDelta, MirrorDeltaDatum.deltaTzNegHalf_keV,
    MirrorDeltaDatum.deltaTzPosHalf_keV, A9_Be_B]

theorem A13_delta_within_error : withinReportedError A13_C_N := by
  norm_num [withinReportedError, centralDelta, mirrorDelta,
    MirrorDeltaDatum.deltaTzNegHalf_keV, MirrorDeltaDatum.deltaTzPosHalf_keV,
    MirrorDeltaDatum.reportedDelta_keV, MirrorDeltaDatum.reportedError_keV,
    A13_C_N]

theorem A15_delta_exact : centralDelta A15_N_O = 64 / 10 := by
  norm_num [centralDelta, mirrorDelta, MirrorDeltaDatum.deltaTzNegHalf_keV,
    MirrorDeltaDatum.deltaTzPosHalf_keV, A15_N_O]

theorem A17_delta_within_error : withinReportedError A17_O_F := by
  norm_num [withinReportedError, centralDelta, mirrorDelta,
    MirrorDeltaDatum.deltaTzNegHalf_keV, MirrorDeltaDatum.deltaTzPosHalf_keV,
    MirrorDeltaDatum.reportedDelta_keV, MirrorDeltaDatum.reportedError_keV,
    A17_O_F]

theorem A19_delta_within_error : withinReportedError A19_F_Ne := by
  norm_num [withinReportedError, centralDelta, mirrorDelta,
    MirrorDeltaDatum.deltaTzNegHalf_keV, MirrorDeltaDatum.deltaTzPosHalf_keV,
    MirrorDeltaDatum.reportedDelta_keV, MirrorDeltaDatum.reportedError_keV,
    A19_F_Ne]

theorem A23_delta_exact : centralDelta A23_Na_Mg = 106 / 10 := by
  norm_num [centralDelta, mirrorDelta, MirrorDeltaDatum.deltaTzNegHalf_keV,
    MirrorDeltaDatum.deltaTzPosHalf_keV, A23_Na_Mg]

theorem A25_delta_near_zero : withinReportedError A25_Mg_Al := by
  norm_num [withinReportedError, centralDelta, mirrorDelta,
    MirrorDeltaDatum.deltaTzNegHalf_keV, MirrorDeltaDatum.deltaTzPosHalf_keV,
    MirrorDeltaDatum.reportedDelta_keV, MirrorDeltaDatum.reportedError_keV,
    A25_Mg_Al]

theorem A29_delta_within_error : withinReportedError A29_Si_P := by
  norm_num [withinReportedError, centralDelta, mirrorDelta,
    MirrorDeltaDatum.deltaTzNegHalf_keV, MirrorDeltaDatum.deltaTzPosHalf_keV,
    MirrorDeltaDatum.reportedDelta_keV, MirrorDeltaDatum.reportedError_keV,
    A29_Si_P]

def nearZeroBand (x : ℚ) : Prop :=
  |x| ≤ 50

theorem A25_in_50keV_band : nearZeroBand (centralDelta A25_Mg_Al) := by
  norm_num [nearZeroBand, centralDelta, mirrorDelta,
    MirrorDeltaDatum.deltaTzNegHalf_keV, MirrorDeltaDatum.deltaTzPosHalf_keV,
    A25_Mg_Al]

theorem A13_outside_50keV_band : ¬ nearZeroBand (centralDelta A13_C_N) := by
  norm_num [nearZeroBand, centralDelta, mirrorDelta,
    MirrorDeltaDatum.deltaTzNegHalf_keV, MirrorDeltaDatum.deltaTzPosHalf_keV,
    A13_C_N]

theorem A17_outside_50keV_band : ¬ nearZeroBand (centralDelta A17_O_F) := by
  norm_num [nearZeroBand, centralDelta, mirrorDelta,
    MirrorDeltaDatum.deltaTzNegHalf_keV, MirrorDeltaDatum.deltaTzPosHalf_keV,
    A17_O_F]

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

end CakirliPnInteractionIsospin

end noncomputable section
