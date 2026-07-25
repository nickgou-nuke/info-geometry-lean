import Mathlib.Tactic
import InfoGeometry.External.Auto.A67MirrorE1

noncomputable section

namespace BizzetiA67IVGMR

open A67MirrorE1

def mirrorAsymmetryRatio (eps : ℚ) : ℚ :=
  ((1 + eps) / (1 - eps)) ^ 2

theorem mirrorAsymmetryRatio_zero :
    mirrorAsymmetryRatio 0 = 1 := by
  norm_num [mirrorAsymmetryRatio]

def uniformOneBody : ℚ := 752 / 1000
def uniformTwoBody : ℚ := 410 / 1000
def uniformEta : ℚ := (uniformOneBody - uniformTwoBody) / uniformOneBody

theorem uniformEta_exact :
    uniformEta = 171 / 376 := by
  norm_num [uniformEta, uniformOneBody, uniformTwoBody]

theorem uniformEta_window :
    (45 / 100 : ℚ) < uniformEta ∧ uniformEta < (46 / 100 : ℚ) := by
  norm_num [uniformEta, uniformOneBody, uniformTwoBody]

def woodsSaxonEta : ℚ := 445 / 1000

theorem woodsSaxonEta_window :
    (44 / 100 : ℚ) < woodsSaxonEta ∧ woodsSaxonEta < (45 / 100 : ℚ) := by
  norm_num [woodsSaxonEta]

def epsMinus_uniform_A1_negligible : ℚ := -(872 / 10000)
def epsMinus_uniform_A0_negligible : ℚ := 120 / 1000
def epsMinus_woodsSaxon_A1_negligible : ℚ := -(852 / 10000)
def epsMinus_woodsSaxon_A0_negligible : ℚ := 116 / 1000

def R_uniform_A1_negligible : ℚ :=
  mirrorAsymmetryRatio epsMinus_uniform_A1_negligible

def R_uniform_A0_negligible : ℚ :=
  mirrorAsymmetryRatio epsMinus_uniform_A0_negligible

def R_woodsSaxon_A1_negligible : ℚ :=
  mirrorAsymmetryRatio epsMinus_woodsSaxon_A1_negligible

def R_woodsSaxon_A0_negligible : ℚ :=
  mirrorAsymmetryRatio epsMinus_woodsSaxon_A0_negligible

theorem R_uniform_A1_negligible_exact :
    R_uniform_A1_negligible = 1301881 / 1846881 := by
  norm_num [R_uniform_A1_negligible, mirrorAsymmetryRatio,
    epsMinus_uniform_A1_negligible]

theorem R_uniform_A1_negligible_window :
    (70 / 100 : ℚ) < R_uniform_A1_negligible ∧
      R_uniform_A1_negligible < (71 / 100 : ℚ) := by
  norm_num [R_uniform_A1_negligible, mirrorAsymmetryRatio,
    epsMinus_uniform_A1_negligible]

theorem R_uniform_A0_negligible_exact :
    R_uniform_A0_negligible = 196 / 121 := by
  norm_num [R_uniform_A0_negligible, mirrorAsymmetryRatio,
    epsMinus_uniform_A0_negligible]

theorem R_uniform_A0_negligible_window :
    (161 / 100 : ℚ) < R_uniform_A0_negligible ∧
      R_uniform_A0_negligible < (162 / 100 : ℚ) := by
  norm_num [R_uniform_A0_negligible, mirrorAsymmetryRatio,
    epsMinus_uniform_A0_negligible]

theorem R_woodsSaxon_A1_negligible_window :
    (70 / 100 : ℚ) < R_woodsSaxon_A1_negligible ∧
      R_woodsSaxon_A1_negligible < (72 / 100 : ℚ) := by
  norm_num [R_woodsSaxon_A1_negligible, mirrorAsymmetryRatio,
    epsMinus_woodsSaxon_A1_negligible]

theorem R_woodsSaxon_A0_negligible_window :
    (158 / 100 : ℚ) < R_woodsSaxon_A0_negligible ∧
      R_woodsSaxon_A0_negligible < (160 / 100 : ℚ) := by
  norm_num [R_woodsSaxon_A0_negligible, mirrorAsymmetryRatio,
    epsMinus_woodsSaxon_A0_negligible]

def higherOrderUpperRelative : ℚ := 1 / 1000

theorem higherOrder_is_three_orders_lower :
    higherOrderUpperRelative = (1 / 10 : ℚ) ^ 3 := by
  norm_num [higherOrderUpperRelative]

structure RadialIntegralRow where
  label : String
  sphere : ℚ
  extrapolated : ℚ
  woodsSaxon : ℚ

def f7_rDeltafc_g9 : RadialIntegralRow where
  label := "f7/2-rDeltafc-g9/2"
  sphere := 700 / 1000
  extrapolated := 752 / 1000
  woodsSaxon := 739 / 1000

def g9_Deltafc_g9 : RadialIntegralRow where
  label := "g9/2-Deltafc-g9/2"
  sphere := 697 / 1000
  extrapolated := 749 / 1000
  woodsSaxon := 735 / 1000

def f7_Deltafc_f7 : RadialIntegralRow where
  label := "f7/2-Deltafc-f7/2"
  sphere := 594 / 1000
  extrapolated := 625 / 1000
  woodsSaxon := 620 / 1000

def pfAverageLowerShell : ℚ := 615 / 1000

theorem twoBodyCoefficient_from_pfAverage :
    (2 / 3 : ℚ) * pfAverageLowerShell = 41 / 100 := by
  norm_num [pfAverageLowerShell]

theorem radial_one_body_extrapolated_eq_uniformOneBody :
    f7_rDeltafc_g9.extrapolated = uniformOneBody := by
  rfl

def IVGMREpsilon
    (C radialNumerator radialDenominator eta A1 A0 : ℚ) : ℚ :=
  3 * C * (radialNumerator / radialDenominator) *
    ((eta * A1 - A0) / (A1 + 3 * A0))

theorem IVGMREpsilon_denominator_nonzero_uniform_A1 :
    (1 + 3 * (0 : ℚ)) ≠ 0 := by
  norm_num

theorem formalSummary :
    mirrorChargesExchange As67Se67 ∧
      uniformEta = 171 / 376 ∧
      (70 / 100 : ℚ) < R_uniform_A1_negligible ∧
      R_uniform_A1_negligible < (71 / 100 : ℚ) ∧
      (161 / 100 : ℚ) < R_uniform_A0_negligible ∧
      R_uniform_A0_negligible < (162 / 100 : ℚ) ∧
      higherOrderUpperRelative = (1 / 10 : ℚ) ^ 3 := by
  exact ⟨As67Se67_is_mirror, uniformEta_exact,
    R_uniform_A1_negligible_window.1,
    R_uniform_A1_negligible_window.2,
    R_uniform_A0_negligible_window.1,
    R_uniform_A0_negligible_window.2,
    higherOrder_is_three_orders_lower⟩

end BizzetiA67IVGMR

end noncomputable section
