theory CKMAeonColimit
  imports Complex_Main
begin

definition aeonCount :: nat where "aeonCount = 3"
definition generationCount :: nat where "generationCount = 3"
definition ckmParameters :: nat where "ckmParameters = 4"
definition ckmEntries :: nat where "ckmEntries = 9"
definition threeGenerationWeylCount :: nat where "threeGenerationWeylCount = 48"
definition stablePage :: nat where "stablePage = 3"
definition serreResidueRank :: nat where "serreResidueRank = 8"
definition aeonColimitRank :: nat where "aeonColimitRank = 24"
definition su3Generators :: nat where "su3Generators = 8"
definition su2Generators :: nat where "su2Generators = 3"
definition smRank :: nat where "smRank = 4"
definition smGenerators :: nat where "smGenerators = 12"
definition cartanGenerators :: nat where "cartanGenerators = 4"
definition C2su3Fund :: rat where "C2su3Fund = 4/3"
definition C2su2Doublet :: rat where "C2su2Doublet = 3/4"
definition upCharge :: rat where "upCharge = 2/3"
definition downCharge :: rat where "downCharge = -1/3"
definition colorAnomaly :: rat where "colorAnomaly = 0"
definition weakAnomaly :: rat where "weakAnomaly = 0"
definition generationAnomaly :: rat where "generationAnomaly = 0"
definition determinantSocket :: rat where "determinantSocket = 1"
definition jarlskogSocket :: rat where "jarlskogSocket = 0"
definition d2Target :: "nat*int" where "d2Target = (2,0)"
definition d2Square :: nat where "d2Square = 0"
definition graphEdges :: nat where "graphEdges = 6"

theorem ckm_aeon_kernel:
  "aeonCount = 3 \<and> generationCount = 3 \<and> ckmParameters = 4 \<and> ckmEntries = 9 \<and> threeGenerationWeylCount = 48 \<and>
   stablePage = 3 \<and> serreResidueRank = 8 \<and> aeonColimitRank = 24 \<and>
   su3Generators = 8 \<and> su2Generators = 3 \<and> smRank = 4 \<and> smGenerators = 12 \<and> cartanGenerators = 4 \<and>
   C2su3Fund = 4/3 \<and> C2su2Doublet = 3/4 \<and> upCharge = 2/3 \<and> downCharge = -1/3 \<and>
   colorAnomaly = 0 \<and> weakAnomaly = 0 \<and> generationAnomaly = 0 \<and> determinantSocket = 1 \<and> jarlskogSocket = 0 \<and>
   d2Target = (2,0) \<and> d2Square = 0 \<and> graphEdges = 6"
  by (simp add: aeonCount_def generationCount_def ckmParameters_def ckmEntries_def threeGenerationWeylCount_def stablePage_def serreResidueRank_def aeonColimitRank_def su3Generators_def su2Generators_def smRank_def smGenerators_def cartanGenerators_def C2su3Fund_def C2su2Doublet_def upCharge_def downCharge_def colorAnomaly_def weakAnomaly_def generationAnomaly_def determinantSocket_def jarlskogSocket_def d2Target_def d2Square_def graphEdges_def)

datatype concept = Aeon_Three_Colimit | CKM_Matrix | SU3_Color | SU2_Weak | U1_Hypercharge | Three_Generation_SM | Anomaly_Cancelled
datatype edge = generates | mixes | carries | cancels
fun edgeHolds :: "concept => edge => concept => bool" where
  "edgeHolds Aeon_Three_Colimit generates CKM_Matrix = True" |
  "edgeHolds CKM_Matrix mixes Three_Generation_SM = True" |
  "edgeHolds Three_Generation_SM carries SU3_Color = True" |
  "edgeHolds Three_Generation_SM carries SU2_Weak = True" |
  "edgeHolds Three_Generation_SM carries U1_Hypercharge = True" |
  "edgeHolds Three_Generation_SM cancels Anomaly_Cancelled = True" |
  "edgeHolds _ _ _ = False"

theorem graph_kernel:
  "edgeHolds Aeon_Three_Colimit generates CKM_Matrix = True \<and>
   edgeHolds CKM_Matrix mixes Three_Generation_SM = True \<and>
   edgeHolds Three_Generation_SM carries SU3_Color = True \<and>
   edgeHolds Three_Generation_SM carries SU2_Weak = True \<and>
   edgeHolds Three_Generation_SM carries U1_Hypercharge = True \<and>
   edgeHolds Three_Generation_SM cancels Anomaly_Cancelled = True"
  by simp

end
