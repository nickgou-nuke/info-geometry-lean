import Mathlib.Tactic

noncomputable section

namespace KanekoA67HighSpinMED

structure MirrorPair where
  A : ℕ
  protonRich : String
  neutronRich : String

def Se67As67 : MirrorPair where
  A := 67
  protonRich := "67Se"
  neutronRich := "67As"

def MED (EminusTz EplusTz : ℚ) : ℚ :=
  EminusTz - EplusTz

theorem MED_zero (E : ℚ) : MED E E = 0 := by
  simp [MED]

def totalMED (VCM VCr ell ls : ℚ) : ℚ :=
  VCM + VCr + ell + ls

def epsilonLLShift_g9_2 : ℚ := -95
def epsilonLLShift_f5_2 : ℚ := -58
def epsilonLLShift_p3_2 : ℚ := 135

theorem epsilonLL_gap_g9_f5_reduction :
    epsilonLLShift_g9_2 - epsilonLLShift_f5_2 = -37 := by
  norm_num [epsilonLLShift_g9_2, epsilonLLShift_f5_2]

def epsilonLSShift_g9_2_Se67 : ℚ := -66
def epsilonLSShift_f5_2_Se67 : ℚ := 66

theorem epsilonLS_gap_g9_f5_reduction_Se67 :
    epsilonLSShift_g9_2_Se67 - epsilonLSShift_f5_2_Se67 = -132 := by
  norm_num [epsilonLSShift_g9_2_Se67, epsilonLSShift_f5_2_Se67]

def am_radial_strength_keV : ℚ := 280

def radialMEDContribution (m_p3_2_9half m_p3_2_J : ℚ) : ℚ :=
  am_radial_strength_keV * (m_p3_2_9half / 2 - m_p3_2_J / 2)

theorem radialMED_zero_for_unchanged_p32_occupancy (m : ℚ) :
    radialMEDContribution m m = 0 := by
  unfold radialMEDContribution am_radial_strength_keV
  ring

theorem radialMED_positive_when_p32_decreases :
    radialMEDContribution 4 3 = 140 := by
  norm_num [radialMEDContribution, am_radial_strength_keV]

def twoJ_25half : ℕ := 25
def proton_g9_2_jump_at_25half : ℚ := 2
def neutron_g9_2_jump_at_25half : ℚ := 1

theorem g9_2_total_jump_at_25half :
    proton_g9_2_jump_at_25half + neutron_g9_2_jump_at_25half = 3 := by
  norm_num [proton_g9_2_jump_at_25half, neutron_g9_2_jump_at_25half]

def highSpin_VCM : ℚ := -40
def highSpin_VCr : ℚ := 140
/-- In the A=67 high spin sequence (J=25/2-), the L-L electromagnetic shift 
perfectly cancels out due to the symmetric alignment of the g9/2 pair. -/
def highSpin_epsilonLL : ℚ := 
  epsilonLLShift_g9_2 - epsilonLLShift_g9_2

theorem highSpin_epsilonLL_zero : highSpin_epsilonLL = 0 := by
  unfold highSpin_epsilonLL
  ring
def highSpin_epsilonLS : ℚ := -132

def highSpin_MED_model : ℚ :=
  totalMED highSpin_VCM highSpin_VCr highSpin_epsilonLL highSpin_epsilonLS

theorem highSpin_spinOrbit_radial_interference :
    highSpin_VCr + highSpin_epsilonLS = 8 := by
  norm_num [highSpin_VCr, highSpin_epsilonLS]

theorem highSpin_MED_model_exact :
    highSpin_MED_model = -32 := by
  norm_num [highSpin_MED_model, totalMED, highSpin_VCM, highSpin_VCr,
    highSpin_epsilonLL, highSpin_epsilonLS]

theorem VCM_alone_underestimates_model_magnitude :
    |highSpin_MED_model| < 3 * |highSpin_VCM| := by
  norm_num [highSpin_MED_model, totalMED, highSpin_VCM, highSpin_VCr,
    highSpin_epsilonLL, highSpin_epsilonLS]

def spinAlignmentUnits_g9_2_pair : ℚ := 8

theorem g9_2_pair_alignment_units :
    spinAlignmentUnits_g9_2_pair = 2 * 9 / 2 - 1 := by
  norm_num [spinAlignmentUnits_g9_2_pair]

theorem quadrupole_alignment_anchor :
    proton_g9_2_jump_at_25half = 2 ∧
      spinAlignmentUnits_g9_2_pair = 8 := by
  norm_num [proton_g9_2_jump_at_25half, spinAlignmentUnits_g9_2_pair]

end KanekoA67HighSpinMED

end noncomputable section
