theory A47KIsospinMixing
  imports Complex_Main
begin

definition yWeighted :: rat where "yWeighted = -12/125"
definition yWeightedSigma :: rat where "yWeightedSigma = 37/1000"
definition yRecoil :: rat where "yRecoil = -51/500"
definition yRecoilSigma :: rat where "yRecoilSigma = 41/1000"
definition coulombObserved :: rat where "coulombObserved = 90"
definition sigmaObserved :: rat where "sigmaObserved = 35"
definition coulombWeighted :: rat where "coulombWeighted = 72"
definition sigmaWeighted :: rat where "sigmaWeighted = 26"
definition coulombPredicted :: rat where "coulombPredicted = 190"
definition branchHalfToHalf :: rat where "branchHalfToHalf = 4/5"
definition branchThreeHalfKnown :: rat where "branchThreeHalfKnown = 19/100"
definition branchThreeHalfOther :: rat where "branchThreeHalfOther = 1/100"
definition branchThreeHalfTotal :: rat where "branchThreeHalfTotal = branchThreeHalfKnown + branchThreeHalfOther"
definition A_beta_GT_half_to_half :: rat where "A_beta_GT_half_to_half = -2/3"
definition A_beta_GT_half_to_threehalf :: rat where "A_beta_GT_half_to_threehalf = 1/3"
definition weightedPureGTAsymmetry :: rat where "weightedPureGTAsymmetry = branchHalfToHalf*A_beta_GT_half_to_half + branchThreeHalfTotal*A_beta_GT_half_to_threehalf"
definition significance :: "rat => rat => rat" where "significance x sigma = abs x / sigma"
definition relativeToPrediction :: "rat => rat => rat" where "relativeToPrediction obs p = obs/p"
definition deficit :: "rat => rat => rat" where "deficit obs p = 1-obs/p"

theorem a47k_isospin_mixing_kernel:
  "yWeighted = -12/125 \<and> yWeightedSigma = 37/1000 \<and>
   yRecoil = -51/500 \<and> yRecoilSigma = 41/1000 \<and>
   significance yWeighted yWeightedSigma = 96/37 \<and>
   significance yRecoil yRecoilSigma = 102/41 \<and>
   coulombObserved - sigmaObserved = 55 \<and> coulombObserved + sigmaObserved = 125 \<and>
   coulombWeighted - sigmaWeighted = 46 \<and> coulombWeighted + sigmaWeighted = 98 \<and>
   relativeToPrediction coulombObserved coulombPredicted = 9/19 \<and>
   relativeToPrediction coulombWeighted coulombPredicted = 36/95 \<and>
   deficit coulombObserved coulombPredicted = 10/19 \<and>
   deficit coulombWeighted coulombPredicted = 59/95 \<and>
   branchHalfToHalf + branchThreeHalfKnown + branchThreeHalfOther = 1 \<and>
   branchThreeHalfTotal = 1/5 \<and>
   weightedPureGTAsymmetry = -7/15"
  by (simp add: yWeighted_def yWeightedSigma_def yRecoil_def yRecoilSigma_def coulombObserved_def sigmaObserved_def coulombWeighted_def sigmaWeighted_def coulombPredicted_def branchHalfToHalf_def branchThreeHalfKnown_def branchThreeHalfOther_def branchThreeHalfTotal_def A_beta_GT_half_to_half_def A_beta_GT_half_to_threehalf_def weightedPureGTAsymmetry_def significance_def relativeToPrediction_def deficit_def)

datatype concept = A47K_BetaDecay | A47Ca_IsospinMixedState | Fermi_GT_Interference | Analog_Antianalog_Mixing | Coulomb_Mixing_MatrixElement | TOPE_Isovector_Search_Channel
datatype edge = decays_to | measures | implies | compares_with | motivates
fun edgeHolds :: "concept => edge => concept => bool" where
  "edgeHolds A47K_BetaDecay decays_to A47Ca_IsospinMixedState = True" |
  "edgeHolds A47K_BetaDecay measures Fermi_GT_Interference = True" |
  "edgeHolds Fermi_GT_Interference implies Coulomb_Mixing_MatrixElement = True" |
  "edgeHolds Coulomb_Mixing_MatrixElement compares_with Analog_Antianalog_Mixing = True" |
  "edgeHolds Analog_Antianalog_Mixing motivates TOPE_Isovector_Search_Channel = True" |
  "edgeHolds _ _ _ = False"

theorem graph_kernel:
  "edgeHolds A47K_BetaDecay decays_to A47Ca_IsospinMixedState = True \<and>
   edgeHolds A47K_BetaDecay measures Fermi_GT_Interference = True \<and>
   edgeHolds Fermi_GT_Interference implies Coulomb_Mixing_MatrixElement = True \<and>
   edgeHolds Coulomb_Mixing_MatrixElement compares_with Analog_Antianalog_Mixing = True \<and>
   edgeHolds Analog_Antianalog_Mixing motivates TOPE_Isovector_Search_Channel = True"
  by simp

end
