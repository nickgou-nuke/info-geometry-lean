theory PRL124RuPairingSymmetry
  imports Complex_Main
begin

definition A :: nat where "A = 88"
definition Z :: nat where "Z = 44"
definition N :: nat where "N = 44"
definition twoTz :: int where "twoTz = int N - int Z"
definition su2SpinGenerators :: nat where "su2SpinGenerators = 3"
definition su2IsospinGenerators :: nat where "su2IsospinGenerators = 3"
definition cartanGenerators :: nat where "cartanGenerators = 2"
definition totalGenerators :: nat where "totalGenerators = su2SpinGenerators + su2IsospinGenerators"
definition spinC2I14 :: nat where "spinC2I14 = 14*15"
definition isospinC2T1 :: nat where "isospinC2T1 = 1*2"
definition isovectorPairT :: nat where "isovectorPairT = 1"
definition isovectorPairI :: nat where "isovectorPairI = 0"
definition isoscalarPairT :: nat where "isoscalarPairT = 0"
definition isoscalarPairImin :: nat where "isoscalarPairImin = 1"
definition isovectorMultiplicity :: nat where "isovectorMultiplicity = 3"
definition isoscalarMultiplicity :: nat where "isoscalarMultiplicity = 3"
definition bandLength :: nat where "bandLength = 8"
definition gammaSum :: nat where "gammaSum = 1063+1153+1253"
definition omegaNormal :: rat where "omegaNormal = 47/100"
definition omegaRu :: rat where "omegaRu = 54/100"
definition omegaDelay :: rat where "omegaDelay = omegaRu - omegaNormal"
definition omegaRatio :: rat where "omegaRatio = omegaRu / omegaNormal"
definition fpgdDegeneracy :: nat where "fpgdDegeneracy = 2+4+6+10+6"
definition fpgdPN :: nat where "fpgdPN = 2*fpgdDegeneracy"
definition reactionA :: nat where "reactionA = 36+54-2"
definition reactionZ :: nat where "reactionZ = 18+26"
definition hamiltonianTerms :: nat where "hamiltonianTerms = 4"
definition graphEdges :: nat where "graphEdges = 6"

theorem prl124_ru_pairing_kernel:
  "A = 88 \<and> Z = 44 \<and> N = 44 \<and> twoTz = 0 \<and>
   su2SpinGenerators = 3 \<and> su2IsospinGenerators = 3 \<and> cartanGenerators = 2 \<and> totalGenerators = 6 \<and>
   spinC2I14 = 210 \<and> isospinC2T1 = 2 \<and>
   isovectorPairT = 1 \<and> isovectorPairI = 0 \<and> isoscalarPairT = 0 \<and> isoscalarPairImin = 1 \<and>
   isovectorMultiplicity = 3 \<and> isoscalarMultiplicity = 3 \<and> bandLength = 8 \<and> gammaSum = 3469 \<and>
   omegaDelay = 7/100 \<and> omegaRatio = 54/47 \<and>
   fpgdDegeneracy = 28 \<and> fpgdPN = 56 \<and> reactionA = 88 \<and> reactionZ = 44 \<and>
   hamiltonianTerms = 4 \<and> graphEdges = 6"
  by (simp add: A_def Z_def N_def twoTz_def su2SpinGenerators_def su2IsospinGenerators_def cartanGenerators_def totalGenerators_def spinC2I14_def isospinC2T1_def isovectorPairT_def isovectorPairI_def isoscalarPairT_def isoscalarPairImin_def isovectorMultiplicity_def isoscalarMultiplicity_def bandLength_def gammaSum_def omegaNormal_def omegaRu_def omegaDelay_def omegaRatio_def fpgdDegeneracy_def fpgdPN_def reactionA_def reactionZ_def hamiltonianTerms_def graphEdges_def)

datatype concept = Ru88_NeqZ | SU2_Spin | SU2_Isospin | Isovector_T1_I0_Pair | Isoscalar_T0_Igt0_Pair | Delayed_Rotational_Alignment | FPGD_Model_Space
datatype edge = has_symmetry | carries_pair | witnesses | uses_space
fun edgeHolds :: "concept => edge => concept => bool" where
  "edgeHolds Ru88_NeqZ has_symmetry SU2_Spin = True" |
  "edgeHolds Ru88_NeqZ has_symmetry SU2_Isospin = True" |
  "edgeHolds Ru88_NeqZ carries_pair Isovector_T1_I0_Pair = True" |
  "edgeHolds Ru88_NeqZ carries_pair Isoscalar_T0_Igt0_Pair = True" |
  "edgeHolds Isoscalar_T0_Igt0_Pair witnesses Delayed_Rotational_Alignment = True" |
  "edgeHolds Ru88_NeqZ uses_space FPGD_Model_Space = True" |
  "edgeHolds _ _ _ = False"

theorem graph_kernel:
  "edgeHolds Ru88_NeqZ has_symmetry SU2_Spin = True \<and>
   edgeHolds Ru88_NeqZ has_symmetry SU2_Isospin = True \<and>
   edgeHolds Ru88_NeqZ carries_pair Isovector_T1_I0_Pair = True \<and>
   edgeHolds Ru88_NeqZ carries_pair Isoscalar_T0_Igt0_Pair = True \<and>
   edgeHolds Isoscalar_T0_Igt0_Pair witnesses Delayed_Rotational_Alignment = True \<and>
   edgeHolds Ru88_NeqZ uses_space FPGD_Model_Space = True"
  by simp

end
