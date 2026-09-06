import Mathlib

noncomputable section

namespace A47KIsospinMixing

abbrev Q := ℚ

def A : Q := 47
def ZCa : Q := 20
def parent : String := "47K"
def daughter : String := "47Ca"
def spinParity : String := "1/2+"

def yWeighted : Q := -12 / 125
def yWeightedAbs : Q := 12 / 125
def yWeightedSigma : Q := 37 / 1000
def yRecoil : Q := -51 / 500
def yRecoilAbs : Q := 51 / 500
def yRecoilSigma : Q := 41 / 1000

def coulombMixingObserved_keV : Q := 90
def coulombMixingObservedSigma_keV : Q := 35
def coulombMixingWeighted_keV : Q := 72
def coulombMixingWeightedSigma_keV : Q := 26
def coulombMixingPredicted_keV : Q := 190

def branchHalfToHalf : Q := 4 / 5
def branchThreeHalfKnown : Q := 19 / 100
def branchThreeHalfOther : Q := 1 / 100
def branchThreeHalfTotal : Q := branchThreeHalfKnown + branchThreeHalfOther

def A_beta_GT_half_to_half : Q := -2 / 3
def A_beta_GT_half_to_threehalf : Q := 1 / 3

def weightedPureGTAsymmetry : Q :=
  branchHalfToHalf * A_beta_GT_half_to_half + branchThreeHalfTotal * A_beta_GT_half_to_threehalf

def experimentalMGTAbs : Q := 3 / 10
def singleParticleGTAbsSq : Q := 3

def ratio (x y : Q) : Q := x / y
def absoluteErrorInterval (center sigma : Q) : Q × Q := (center - sigma, center + sigma)
def relativeToPrediction (observed predicted : Q) : Q := observed / predicted
def removedFragmentationFraction (observed predicted : Q) : Q := 1 - observed / predicted
def significance (absval sigma : Q) : Q := absval / sigma

theorem extracted_y_weighted : yWeighted = -12 / 125 ∧ yWeightedSigma = 37 / 1000 := by
  norm_num [yWeighted, yWeightedSigma]

theorem extracted_y_recoil : yRecoil = -51 / 500 ∧ yRecoilSigma = 41 / 1000 := by
  norm_num [yRecoil, yRecoilSigma]

theorem y_weighted_significance : significance yWeightedAbs yWeightedSigma = 96 / 37 := by
  norm_num [significance, yWeightedAbs, yWeightedSigma]

theorem y_recoil_significance : significance yRecoilAbs yRecoilSigma = 102 / 41 := by
  norm_num [significance, yRecoilAbs, yRecoilSigma]

theorem observed_coulomb_interval :
    absoluteErrorInterval coulombMixingObserved_keV coulombMixingObservedSigma_keV = (55, 125) := by
  norm_num [absoluteErrorInterval, coulombMixingObserved_keV, coulombMixingObservedSigma_keV]

theorem weighted_coulomb_interval :
    absoluteErrorInterval coulombMixingWeighted_keV coulombMixingWeightedSigma_keV = (46, 98) := by
  norm_num [absoluteErrorInterval, coulombMixingWeighted_keV, coulombMixingWeightedSigma_keV]

theorem observed_to_predicted_ratio :
    relativeToPrediction coulombMixingObserved_keV coulombMixingPredicted_keV = 9 / 19 := by
  norm_num [relativeToPrediction, coulombMixingObserved_keV, coulombMixingPredicted_keV]

theorem weighted_to_predicted_ratio :
    relativeToPrediction coulombMixingWeighted_keV coulombMixingPredicted_keV = 36 / 95 := by
  norm_num [relativeToPrediction, coulombMixingWeighted_keV, coulombMixingPredicted_keV]

theorem observed_deficit_fraction :
    removedFragmentationFraction coulombMixingObserved_keV coulombMixingPredicted_keV = 10 / 19 := by
  norm_num [removedFragmentationFraction, coulombMixingObserved_keV, coulombMixingPredicted_keV]

theorem weighted_deficit_fraction :
    removedFragmentationFraction coulombMixingWeighted_keV coulombMixingPredicted_keV = 59 / 95 := by
  norm_num [removedFragmentationFraction, coulombMixingWeighted_keV, coulombMixingPredicted_keV]

theorem branch_partition : branchHalfToHalf + branchThreeHalfKnown + branchThreeHalfOther = 1 := by
  norm_num [branchHalfToHalf, branchThreeHalfKnown, branchThreeHalfOther]

theorem branch_threehalf_total : branchThreeHalfTotal = 1 / 5 := by
  norm_num [branchThreeHalfTotal, branchThreeHalfKnown, branchThreeHalfOther]

theorem weighted_GT_asymmetry_exact : weightedPureGTAsymmetry = -7 / 15 := by
  norm_num [weightedPureGTAsymmetry, branchHalfToHalf, branchThreeHalfTotal,
    branchThreeHalfKnown, branchThreeHalfOther, A_beta_GT_half_to_half, A_beta_GT_half_to_threehalf]

theorem weighted_GT_asymmetry_close_to_paper_anchor :
    |weightedPureGTAsymmetry - (-467 / 1000)| = 1 / 3000 := by
  norm_num [weightedPureGTAsymmetry, branchHalfToHalf, branchThreeHalfTotal,
    branchThreeHalfKnown, branchThreeHalfOther, A_beta_GT_half_to_half, A_beta_GT_half_to_threehalf]

theorem MGT_abs_anchor : experimentalMGTAbs = 3 / 10 := by
  norm_num [experimentalMGTAbs]

inductive Concept where
  | A47K_BetaDecay
  | A47Ca_IsospinMixedState
  | Fermi_GT_Interference
  | Analog_Antianalog_Mixing
  | Coulomb_Mixing_MatrixElement
  | TOPE_Isovector_Search_Channel
  deriving DecidableEq, Repr

inductive Edge where
  | decays_to
  | measures
  | implies
  | compares_with
  | motivates
  deriving DecidableEq, Repr

def edgeHolds : Concept → Edge → Concept → Bool
  | Concept.A47K_BetaDecay, Edge.decays_to, Concept.A47Ca_IsospinMixedState => true
  | Concept.A47K_BetaDecay, Edge.measures, Concept.Fermi_GT_Interference => true
  | Concept.Fermi_GT_Interference, Edge.implies, Concept.Coulomb_Mixing_MatrixElement => true
  | Concept.Coulomb_Mixing_MatrixElement, Edge.compares_with, Concept.Analog_Antianalog_Mixing => true
  | Concept.Analog_Antianalog_Mixing, Edge.motivates, Concept.TOPE_Isovector_Search_Channel => true
  | _, _, _ => false

theorem graph_kernel :
    edgeHolds Concept.A47K_BetaDecay Edge.decays_to Concept.A47Ca_IsospinMixedState = true ∧
    edgeHolds Concept.A47K_BetaDecay Edge.measures Concept.Fermi_GT_Interference = true ∧
    edgeHolds Concept.Fermi_GT_Interference Edge.implies Concept.Coulomb_Mixing_MatrixElement = true ∧
    edgeHolds Concept.Coulomb_Mixing_MatrixElement Edge.compares_with Concept.Analog_Antianalog_Mixing = true ∧
    edgeHolds Concept.Analog_Antianalog_Mixing Edge.motivates Concept.TOPE_Isovector_Search_Channel = true := by
  decide

theorem a47k_isospin_mixing_kernel :
    yWeighted = -12 / 125 ∧ yWeightedSigma = 37 / 1000 ∧
    yRecoil = -51 / 500 ∧ yRecoilSigma = 41 / 1000 ∧
    significance yWeightedAbs yWeightedSigma = 96 / 37 ∧
    significance yRecoilAbs yRecoilSigma = 102 / 41 ∧
    absoluteErrorInterval coulombMixingObserved_keV coulombMixingObservedSigma_keV = (55,125) ∧
    absoluteErrorInterval coulombMixingWeighted_keV coulombMixingWeightedSigma_keV = (46,98) ∧
    relativeToPrediction coulombMixingObserved_keV coulombMixingPredicted_keV = 9 / 19 ∧
    relativeToPrediction coulombMixingWeighted_keV coulombMixingPredicted_keV = 36 / 95 ∧
    removedFragmentationFraction coulombMixingObserved_keV coulombMixingPredicted_keV = 10 / 19 ∧
    branchHalfToHalf + branchThreeHalfKnown + branchThreeHalfOther = 1 ∧
    branchThreeHalfTotal = 1 / 5 ∧
    weightedPureGTAsymmetry = -7 / 15 := by
  exact ⟨extracted_y_weighted.1, extracted_y_weighted.2, extracted_y_recoil.1,
    extracted_y_recoil.2, y_weighted_significance, y_recoil_significance,
    observed_coulomb_interval, weighted_coulomb_interval, observed_to_predicted_ratio,
    weighted_to_predicted_ratio, observed_deficit_fraction, branch_partition,
    branch_threehalf_total, weighted_GT_asymmetry_exact⟩

end A47KIsospinMixing

end noncomputable section
