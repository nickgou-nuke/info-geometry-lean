import Mathlib

/-!
# Farnea et al. `64Ge` isospin-mixing formal anchors

Rational formal core for Physics Letters B 551 (2003) 56--62,
`Isospin mixing in the N = Z nucleus 64Ge`.
-/

noncomputable section

namespace FarneaGe64IsospinMixing

def isNZ (N Z : ℚ) : Prop := N = Z
def massNumber (N Z : ℚ) : ℚ := N + Z
def T3 (Z N : ℚ) : ℚ := (Z - N) / 2

theorem Ge64_NZ :
    isNZ 32 32 ∧ massNumber 32 32 = 64 ∧ T3 32 32 = 0 := by
  norm_num [isNZ, massNumber, T3]

def fusionEvaporationMass (target projectile alphaCount : ℚ) : ℚ :=
  target + projectile - 4 * alphaCount

theorem Ca40_S32_twoAlpha_to_Ge64 :
    fusionEvaporationMass 40 32 2 = 64 := by
  norm_num [fusionEvaporationMass]

def largeMixingDelta : ℚ := -(39 / 10)
def smallMixingDelta : ℚ := -(9 / 100)
def chi2_largeDelta : ℚ := 54 / 100
def chi2_smallDelta : ℚ := 80 / 100

def quadrupoleContent (delta : ℚ) : ℚ :=
  delta ^ 2 / (1 + delta ^ 2)

theorem large_delta_statistically_favoured :
    chi2_largeDelta < chi2_smallDelta := by
  norm_num [chi2_largeDelta, chi2_smallDelta]

theorem large_delta_quadrupole_content_exact :
    quadrupoleContent largeMixingDelta = 1521 / 1621 := by
  norm_num [quadrupoleContent, largeMixingDelta]

theorem large_delta_quadrupole_content_above_93_percent :
    (93 / 100 : ℚ) < quadrupoleContent largeMixingDelta := by
  norm_num [quadrupoleContent, largeMixingDelta]

def tau9_upper_ps : ℚ := 4
def tau7_ps : ℚ := 431 / 10
def tau5_ps : ℚ := 242 / 10
def lambda7_ps_inv : ℚ := 232 / 10000
def lambda5_ps_inv : ℚ := 41 / 1000

theorem reported_lifetime_order :
    tau9_upper_ps < tau5_ps ∧ tau5_ps < tau7_ps := by
  norm_num [tau9_upper_ps, tau5_ps, tau7_ps]

theorem lambda7_reciprocal_matches_reported_tau_window :
    (43 : ℚ) < 1 / lambda7_ps_inv ∧ 1 / lambda7_ps_inv < 432 / 10 := by
  norm_num [lambda7_ps_inv]

def I1665 : ℚ := 567
def I1048 : ℚ := 130
def I747 : ℚ := 89
def total_5minus_branch_intensity : ℚ := I1665 + I1048 + I747

theorem branch_intensity_sum :
    total_5minus_branch_intensity = 786 := by
  norm_num [total_5minus_branch_intensity, I1665, I1048, I747]

theorem branch_1665_dominates :
    I1048 + I747 < I1665 := by
  norm_num [I1665, I1048, I747]

def BE1_64Ge_Wu : ℚ := 247 / 1000000000
def BM2_64Ge_Wu : ℚ := 606 / 100
def BE1_66Ge_Wu : ℚ := 37 / 10000000
def BM2_66Ge_Wu : ℚ := 39 / 10000
def BM2_68Ge_Wu : ℚ := 71 / 100

theorem BE1_64Ge_order_of_magnitude_below_66Ge :
    BE1_64Ge_Wu / BE1_66Ge_Wu = 247 / 3700 ∧
      BE1_64Ge_Wu < BE1_66Ge_Wu := by
  norm_num [BE1_64Ge_Wu, BE1_66Ge_Wu]

theorem BM2_64Ge_large_against_66Ge :
    BM2_64Ge_Wu / BM2_66Ge_Wu = 20200 / 13 := by
  norm_num [BM2_64Ge_Wu, BM2_66Ge_Wu]

theorem BM2_64Ge_above_68Ge :
    BM2_68Ge_Wu < BM2_64Ge_Wu := by
  norm_num [BM2_68Ge_Wu, BM2_64Ge_Wu]

def BE2_64Ge_747_Wu : ℚ := 1
def BE2_66Ge_886_Wu : ℚ := 4 / 10

theorem weak_E2_ratio :
    BE2_64Ge_747_Wu / BE2_66Ge_886_Wu = 5 / 2 := by
  norm_num [BE2_64Ge_747_Wu, BE2_66Ge_886_Wu]

def alphaDifference (alpha_i alpha_f : ℚ) : ℚ :=
  alpha_i - alpha_f

def Eq6AmplitudeScale (alpha_i alpha_f : ℚ) : ℚ :=
  (2 / 3) * (alphaDifference alpha_i alpha_f) ^ 2

def Eq7BE1_64_from_66 (alpha2 BE1_66 : ℚ) : ℚ :=
  (8 / 3) * alpha2 * BE1_66

def alpha2_from_BE1 (BE1_64 BE1_66 : ℚ) : ℚ :=
  (3 / 8) * (BE1_64 / BE1_66)

theorem Eq7_alpha_symmetric_mixing :
    Eq6AmplitudeScale 1 (-1) = 8 / 3 := by
  norm_num [Eq6AmplitudeScale, alphaDifference]

def alpha2_extracted : ℚ := alpha2_from_BE1 BE1_64Ge_Wu BE1_66Ge_Wu

theorem alpha2_extracted_exact :
    alpha2_extracted = 741 / 29600 := by
  norm_num [alpha2_extracted, alpha2_from_BE1, BE1_64Ge_Wu, BE1_66Ge_Wu]

theorem alpha2_extracted_percent :
    100 * alpha2_extracted = 741 / 296 := by
  norm_num [alpha2_extracted, alpha2_from_BE1, BE1_64Ge_Wu, BE1_66Ge_Wu]

theorem alpha2_extracted_reported_window :
    (24 / 1000 : ℚ) < alpha2_extracted ∧
      alpha2_extracted < (26 / 1000 : ℚ) := by
  norm_num [alpha2_extracted, alpha2_from_BE1, BE1_64Ge_Wu, BE1_66Ge_Wu]

def formalSummary : Prop :=
  isNZ 32 32 ∧
    massNumber 32 32 = 64 ∧
    T3 32 32 = 0 ∧
    quadrupoleContent largeMixingDelta = 1521 / 1621 ∧
    BE1_64Ge_Wu / BE1_66Ge_Wu = 247 / 3700 ∧
    alpha2_extracted = 741 / 29600 ∧
    100 * alpha2_extracted = 741 / 296

theorem formalSummary_proved : formalSummary := by
  exact ⟨Ge64_NZ.1, Ge64_NZ.2.1, Ge64_NZ.2.2,
    large_delta_quadrupole_content_exact,
    BE1_64Ge_order_of_magnitude_below_66Ge.1,
    alpha2_extracted_exact, alpha2_extracted_percent⟩

end FarneaGe64IsospinMixing

end noncomputable section
