theory StrongCPAeonTheta
  imports Complex_Main
begin

definition aeonCount :: nat where "aeonCount = 3"
definition thetaAeonIndex :: nat where "thetaAeonIndex = 3"
definition thetaSedimentWeight :: rat where "thetaSedimentWeight = 1/1000"
definition inverseThetaScale :: rat where "inverseThetaScale = 1000"
definition su3Rank :: nat where "su3Rank = 2"
definition su3Roots :: nat where "su3Roots = 6"
definition su3Cartan :: nat where "su3Cartan = 2"
definition su3Generators :: nat where "su3Generators = 8"
definition su3WeylOrder :: nat where "su3WeylOrder = 6"
definition smRank :: nat where "smRank = 4"
definition smGenerators :: nat where "smGenerators = 12"
definition C2su3Fund :: rat where "C2su3Fund = 4/3"
definition C2su3Adj :: rat where "C2su3Adj = 3"
definition topologicalChargePair :: int where "topologicalChargePair = 0"
definition pontryaginGenerators :: nat where "pontryaginGenerators = 1"
definition thetaIdealGenerators :: nat where "thetaIdealGenerators = 2"
definition dmoduleCCRGenerators :: nat where "dmoduleCCRGenerators = 1"
definition u1AxialAnomalyCoeff :: nat where "u1AxialAnomalyCoeff = 8"
definition generationAnomaly :: rat where "generationAnomaly = 0"
definition d2Target :: "nat*int" where "d2Target = (2,0)"
definition d2Square :: nat where "d2Square = 0"
definition graphEdges :: nat where "graphEdges = 5"

theorem strong_cp_kernel:
  "aeonCount = 3 \<and> thetaAeonIndex = 3 \<and> thetaSedimentWeight = 1/1000 \<and> inverseThetaScale = 1000 \<and>
   su3Rank = 2 \<and> su3Roots = 6 \<and> su3Cartan = 2 \<and> su3Generators = 8 \<and> su3WeylOrder = 6 \<and>
   smRank = 4 \<and> smGenerators = 12 \<and> C2su3Fund = 4/3 \<and> C2su3Adj = 3 \<and>
   topologicalChargePair = 0 \<and> pontryaginGenerators = 1 \<and> thetaIdealGenerators = 2 \<and> dmoduleCCRGenerators = 1 \<and>
   u1AxialAnomalyCoeff = 8 \<and> generationAnomaly = 0 \<and> d2Target = (2,0) \<and> d2Square = 0 \<and> graphEdges = 5"
  by (simp add: aeonCount_def thetaAeonIndex_def thetaSedimentWeight_def inverseThetaScale_def su3Rank_def su3Roots_def su3Cartan_def su3Generators_def su3WeylOrder_def smRank_def smGenerators_def C2su3Fund_def C2su3Adj_def topologicalChargePair_def pontryaginGenerators_def thetaIdealGenerators_def dmoduleCCRGenerators_def u1AxialAnomalyCoeff_def generationAnomaly_def d2Target_def d2Square_def graphEdges_def)

datatype concept = Third_Aeon_Sediment | Theta_Vacuum | SU3_Color | CP_Twist | Axion_Counterterm | Strong_CP_Closure
datatype edge = generates | carries | flips | cancels | closes
fun edgeHolds :: "concept => edge => concept => bool" where
  "edgeHolds Third_Aeon_Sediment generates Theta_Vacuum = True" |
  "edgeHolds Theta_Vacuum carries SU3_Color = True" |
  "edgeHolds CP_Twist flips Theta_Vacuum = True" |
  "edgeHolds Axion_Counterterm cancels Theta_Vacuum = True" |
  "edgeHolds Theta_Vacuum closes Strong_CP_Closure = True" |
  "edgeHolds _ _ _ = False"

theorem graph_kernel:
  "edgeHolds Third_Aeon_Sediment generates Theta_Vacuum = True \<and>
   edgeHolds Theta_Vacuum carries SU3_Color = True \<and>
   edgeHolds CP_Twist flips Theta_Vacuum = True \<and>
   edgeHolds Axion_Counterterm cancels Theta_Vacuum = True \<and>
   edgeHolds Theta_Vacuum closes Strong_CP_Closure = True"
  by simp

end
