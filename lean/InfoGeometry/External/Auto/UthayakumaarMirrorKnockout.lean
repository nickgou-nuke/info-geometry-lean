import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace UthayakumaarMirrorKnockout

structure Nucleus where
  A : ℕ
  Z : ℕ
  N : ℕ

def twoTz (X : Nucleus) : ℤ :=
  (X.N : ℤ) - (X.Z : ℤ)

def isMirrorPair (X Y : Nucleus) : Prop :=
  X.A = Y.A ∧ X.Z = Y.N ∧ X.N = Y.Z

def Mn47 : Nucleus where A := 47; Z := 25; N := 22
def Ti47 : Nucleus where A := 47; Z := 22; N := 25
def Cr45 : Nucleus where A := 45; Z := 24; N := 21
def Sc45 : Nucleus where A := 45; Z := 21; N := 24

theorem Mn47_Ti47_mirror : isMirrorPair Mn47 Ti47 := by
  norm_num [isMirrorPair, Mn47, Ti47]

theorem Cr45_Sc45_mirror : isMirrorPair Cr45 Sc45 := by
  norm_num [isMirrorPair, Cr45, Sc45]

theorem twoTz_Mn47 : twoTz Mn47 = -3 := by
  norm_num [twoTz, Mn47]

theorem twoTz_Ti47 : twoTz Ti47 = 3 := by
  norm_num [twoTz, Ti47]

theorem twoTz_Cr45 : twoTz Cr45 = -3 := by
  norm_num [twoTz, Cr45]

theorem twoTz_Sc45 : twoTz Sc45 = 3 := by
  norm_num [twoTz, Sc45]

theorem mirror_twoTz_cancel_A47 :
    twoTz Mn47 + twoTz Ti47 = 0 := by
  norm_num [twoTz_Mn47, twoTz_Ti47]

theorem mirror_twoTz_cancel_A45 :
    twoTz Cr45 + twoTz Sc45 = 0 := by
  norm_num [twoTz_Cr45, twoTz_Sc45]

def MED (E_protonRich E_neutronRich : ℚ) : ℚ :=
  E_protonRich - E_neutronRich

theorem MED_ground_normalized (E : ℚ) :
    MED E E = 0 := by
  simp [MED]

def suppressionLine (deltaS : ℚ) : ℚ :=
  61 / 100 - (2 / 125) * deltaS

def deltaS_Ti47 : ℚ := 1916 / 1000
def deltaS_Mn47 : ℚ := 1442 / 100

def Rs_Ti47_systematics : ℚ := suppressionLine deltaS_Ti47
def Rs_Mn47_systematics : ℚ := suppressionLine deltaS_Mn47

theorem Rs_Ti47_systematics_exact :
    Rs_Ti47_systematics = 72418 / 125000 := by
  norm_num [Rs_Ti47_systematics, suppressionLine, deltaS_Ti47]

theorem Rs_Mn47_systematics_exact :
    Rs_Mn47_systematics = 4741 / 12500 := by
  norm_num [Rs_Mn47_systematics, suppressionLine, deltaS_Mn47]

theorem stronger_binding_asymmetry_suppresses_Mn47 :
    Rs_Mn47_systematics < Rs_Ti47_systematics := by
  norm_num [Rs_Ti47_systematics, Rs_Mn47_systematics, suppressionLine,
    deltaS_Ti47, deltaS_Mn47]

def tau_Ti47_ps : ℚ := 331
def tau_Ti47_stat_ps : ℚ := 4
def tau_Ti47_sys_ps : ℚ := 15
def tau_Ti47_total_ps : ℚ := 15

def tau_Mn47_ps : ℚ := 687
def tau_Mn47_stat_ps : ℚ := 17
def tau_Mn47_sys_ps : ℚ := 32
def tau_Mn47_total_ps : ℚ := 36

theorem Mn47_lifetime_longer :
    tau_Ti47_ps < tau_Mn47_ps := by
  norm_num [tau_Ti47_ps, tau_Mn47_ps]

theorem Ti47_total_error_bounds_components :
    tau_Ti47_stat_ps ≤ tau_Ti47_total_ps ∧
      tau_Ti47_sys_ps ≤ tau_Ti47_total_ps := by
  norm_num [tau_Ti47_stat_ps, tau_Ti47_sys_ps, tau_Ti47_total_ps]

theorem Mn47_total_error_bounds_components :
    tau_Mn47_stat_ps ≤ tau_Mn47_total_ps ∧
      tau_Mn47_sys_ps ≤ tau_Mn47_total_ps := by
  norm_num [tau_Mn47_stat_ps, tau_Mn47_sys_ps, tau_Mn47_total_ps]

def E_Ti47_7half_keV : ℚ := 1594 / 10
def E_Mn47_7half_keV : ℚ := 1226 / 10

theorem first_excited_energy_MED_A47 :
    MED E_Mn47_7half_keV E_Ti47_7half_keV = -184 / 5 := by
  norm_num [MED, E_Mn47_7half_keV, E_Ti47_7half_keV]

def BM1_Ti47_exp : ℚ := 445 / 10000
def BM1_Mn47_over_Ti47 : ℚ := 97 / 100
def BM1_ratio_error : ℚ := 8 / 100

theorem BM1_ratio_precision_10_percent :
    |BM1_Mn47_over_Ti47 - 1| ≤ (1 / 10 : ℚ) := by
  norm_num [BM1_Mn47_over_Ti47]

theorem BM1_ratio_one_sigma_window :
    (89 / 100 : ℚ) ≤ BM1_Mn47_over_Ti47 ∧
      BM1_Mn47_over_Ti47 ≤ (105 / 100 : ℚ) := by
  norm_num [BM1_Mn47_over_Ti47]

def M1DominanceFraction : ℚ := 99 / 100

theorem M1_almost_pure :
    (9 / 10 : ℚ) < M1DominanceFraction := by
  norm_num [M1DominanceFraction]

def inclusiveCrossSectionAsymmetryFactor : ℚ := 11

theorem inclusiveCrossSectionAsymmetry_large :
    (10 : ℚ) < inclusiveCrossSectionAsymmetryFactor := by
  norm_num [inclusiveCrossSectionAsymmetryFactor]

def spectroscopicFactorCMCorrection : ℚ := 1067 / 1000

theorem cm_correction_positive :
    (1 : ℚ) < spectroscopicFactorCMCorrection := by
  norm_num [spectroscopicFactorCMCorrection]

def formalSummary : Prop :=
  isMirrorPair Mn47 Ti47 ∧ isMirrorPair Cr45 Sc45 ∧
    twoTz Mn47 = -3 ∧ twoTz Ti47 = 3 ∧
    Rs_Mn47_systematics < Rs_Ti47_systematics ∧
    tau_Ti47_ps < tau_Mn47_ps ∧
    |BM1_Mn47_over_Ti47 - 1| ≤ (1 / 10 : ℚ)

theorem formalSummary_proved : formalSummary := by
  exact ⟨Mn47_Ti47_mirror, Cr45_Sc45_mirror,
    twoTz_Mn47, twoTz_Ti47,
    stronger_binding_asymmetry_suppresses_Mn47,
    Mn47_lifetime_longer, BM1_ratio_precision_10_percent⟩

end UthayakumaarMirrorKnockout

end noncomputable section
