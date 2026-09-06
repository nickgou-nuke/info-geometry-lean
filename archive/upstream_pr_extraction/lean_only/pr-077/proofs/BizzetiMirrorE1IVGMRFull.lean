import Mathlib
import proofs.A67MirrorE1
import proofs.BizzetiA67IVGMR

/-!
# Bizzeti--de Angelis--Lenzi--Orlandi mirror E1/IVGMR formal anchors

Formal rational core for
`Isospin Symmetry violation in mirror E1 transitions:
Coherent contributions from the Giant Isovector Monopole Resonance in 67As-67Se`.
-/

noncomputable section

namespace BizzetiMirrorE1IVGMRFull

def T3 (Z N : ℚ) : ℚ :=
  (Z - N) / 2

theorem T3_As67_Se67 :
    T3 33 34 = -(1 / 2) ∧ T3 34 33 = 1 / 2 := by
  norm_num [T3]

structure E1Row where
  energy_keV : ℚ
  BE1 : ℚ
  ME1_abs : ℚ

def As67_725 : E1Row where
  energy_keV := 725
  BE1 := 14 / 10000000
  ME1_abs := 37 / 10000

def Se67_717 : E1Row where
  energy_keV := 717
  BE1 := 4 / 10000000
  ME1_abs := 20 / 10000

def As67_319 : E1Row where
  energy_keV := 319
  BE1 := 83 / 10000000
  ME1_abs := 91 / 10000

def Se67_303_upper : E1Row where
  energy_keV := 303
  BE1 := 14 / 10000000
  ME1_abs := 37 / 10000

theorem tableI_first_BE1_ratio :
    As67_725.BE1 / Se67_717.BE1 = 7 / 2 := by
  norm_num [As67_725, Se67_717]

theorem tableI_first_ME1_ratio :
    As67_725.ME1_abs / Se67_717.ME1_abs = 37 / 20 := by
  norm_num [As67_725, Se67_717]

theorem tableI_second_BE1_ratio_against_upper :
    As67_319.BE1 / Se67_303_upper.BE1 = 83 / 14 := by
  norm_num [As67_319, Se67_303_upper]

theorem tableI_second_ME1_ratio_against_upper :
    As67_319.ME1_abs / Se67_303_upper.ME1_abs = 91 / 37 := by
  norm_num [As67_319, Se67_303_upper]

def extractedMIV : ℚ := 29 / 10000
def extractedMIS : ℚ := 9 / 10000

theorem extracted_isoscalar_fraction :
    extractedMIS / extractedMIV = 9 / 29 := by
  norm_num [extractedMIS, extractedMIV]

def radialCubicSiegertRatio : ℚ := 834 / 1000
def chargeCorrectionAt1MeV : ℚ := 190 / 10000000
def magneticCorrectionAt1MeV : ℚ := 53 / 100000

theorem radialCubicSiegertRatio_exact :
    radialCubicSiegertRatio = 417 / 500 := by
  norm_num [radialCubicSiegertRatio]

theorem higher_order_corrections_subpermille :
    chargeCorrectionAt1MeV < (1 / 1000 : ℚ) ∧
      magneticCorrectionAt1MeV < (1 / 1000 : ℚ) := by
  norm_num [chargeCorrectionAt1MeV, magneticCorrectionAt1MeV]

def IVGMRCoefficient_C : ℚ := 116 / 1000
def IVGMROneBody : ℚ := 752 / 1000
def IVGMRTwoBody : ℚ := 410 / 1000
def IVGMRQuenchEta : ℚ := (IVGMROneBody - IVGMRTwoBody) / IVGMROneBody

theorem IVGMRQuenchEta_exact :
    IVGMRQuenchEta = 171 / 376 := by
  norm_num [IVGMRQuenchEta, IVGMROneBody, IVGMRTwoBody]

theorem IVGMRQuenchEta_decimal_window :
    (45 / 100 : ℚ) < IVGMRQuenchEta ∧
      IVGMRQuenchEta < (46 / 100 : ℚ) := by
  norm_num [IVGMRQuenchEta, IVGMROneBody, IVGMRTwoBody]

def pfShellAverageR2 : ℚ := 615 / 1000

theorem two_body_coefficient_from_pf_average :
    (2 / 3 : ℚ) * pfShellAverageR2 = IVGMRTwoBody := by
  norm_num [pfShellAverageR2, IVGMRTwoBody]

def mirrorAsymmetryRatio (epsMinus : ℚ) : ℚ :=
  ((1 + epsMinus) / (1 - epsMinus)) ^ 2

def eps_A1_negligible : ℚ := -(872 / 10000)
def eps_A0_negligible : ℚ := 120 / 1000
def eps_WS_A1_negligible : ℚ := -(852 / 10000)
def eps_WS_A0_negligible : ℚ := 116 / 1000

theorem ratio_A1_negligible_exact :
    mirrorAsymmetryRatio eps_A1_negligible = 1301881 / 1846881 := by
  norm_num [mirrorAsymmetryRatio, eps_A1_negligible]

theorem ratio_A0_negligible_exact :
    mirrorAsymmetryRatio eps_A0_negligible = 196 / 121 := by
  norm_num [mirrorAsymmetryRatio, eps_A0_negligible]

theorem ratio_WS_A1_negligible_window :
    (70 / 100 : ℚ) < mirrorAsymmetryRatio eps_WS_A1_negligible ∧
      mirrorAsymmetryRatio eps_WS_A1_negligible < (72 / 100 : ℚ) := by
  norm_num [mirrorAsymmetryRatio, eps_WS_A1_negligible]

theorem ratio_WS_A0_negligible_window :
    (158 / 100 : ℚ) < mirrorAsymmetryRatio eps_WS_A0_negligible ∧
      mirrorAsymmetryRatio eps_WS_A0_negligible < (160 / 100 : ℚ) := by
  norm_num [mirrorAsymmetryRatio, eps_WS_A0_negligible]

def Eq60EpsilonKernel
    (C radialRatio eta A1 A0 : ℚ) : ℚ :=
  3 * C * radialRatio * ((eta * A1 - A0) / (A1 + 3 * A0))

theorem Eq60_A0_negligible_epsilon :
    Eq60EpsilonKernel IVGMRCoefficient_C IVGMROneBody IVGMRQuenchEta 1 0 =
      14877 / 125000 := by
  norm_num [Eq60EpsilonKernel, IVGMRCoefficient_C, IVGMROneBody,
    IVGMRQuenchEta, IVGMROneBody, IVGMRTwoBody]

theorem A67_IVGMR_unit_kernel :
    A67MirrorE1.inducedIsoscalarE1Kernel 67 1 1 20 1 1 = 33 / 20 :=
  A67MirrorE1.IVGMR_unit_kernel_A67

def formalSummary : Prop :=
  T3 33 34 = -(1 / 2) ∧
    T3 34 33 = 1 / 2 ∧
    As67_725.BE1 / Se67_717.BE1 = 7 / 2 ∧
    As67_319.BE1 / Se67_303_upper.BE1 = 83 / 14 ∧
    extractedMIS / extractedMIV = 9 / 29 ∧
    chargeCorrectionAt1MeV < (1 / 1000 : ℚ) ∧
    magneticCorrectionAt1MeV < (1 / 1000 : ℚ) ∧
    IVGMRQuenchEta = 171 / 376 ∧
    mirrorAsymmetryRatio eps_A1_negligible = 1301881 / 1846881 ∧
    mirrorAsymmetryRatio eps_A0_negligible = 196 / 121 ∧
    A67MirrorE1.inducedIsoscalarE1Kernel 67 1 1 20 1 1 = 33 / 20

theorem formalSummary_proved : formalSummary := by
  exact ⟨T3_As67_Se67.1, T3_As67_Se67.2,
    tableI_first_BE1_ratio, tableI_second_BE1_ratio_against_upper,
    extracted_isoscalar_fraction, higher_order_corrections_subpermille.1,
    higher_order_corrections_subpermille.2, IVGMRQuenchEta_exact,
    ratio_A1_negligible_exact, ratio_A0_negligible_exact,
    A67_IVGMR_unit_kernel⟩

end BizzetiMirrorE1IVGMRFull

end noncomputable section
