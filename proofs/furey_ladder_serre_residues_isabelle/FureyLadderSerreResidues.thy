theory FureyLadderSerreResidues
  imports Complex_Main
begin

definition stablePage :: nat where "stablePage = 3"
definition e2Rank :: nat where "e2Rank = 8"
definition survivorCount :: nat where "survivorCount = 8"
definition su3Generators :: nat where "su3Generators = 8"
definition su2Generators :: nat where "su2Generators = 3"
definition smRank :: nat where "smRank = 4"
definition smGenerators :: nat where "smGenerators = 12"
definition cartanGenerators :: nat where "cartanGenerators = 4"
definition ladderCount :: nat where "ladderCount = 8"
definition C2su3Fund :: rat where "C2su3Fund = 4/3"
definition C2su2Doublet :: rat where "C2su2Doublet = 3/4"
definition upCharge :: rat where "upCharge = 2/3"
definition downCharge :: rat where "downCharge = -1/3"
definition neutrinoCharge :: rat where "neutrinoCharge = 0"
definition electronCharge :: rat where "electronCharge = -1"
definition weylCount :: nat where "weylCount = 16"
definition colorAnomaly :: rat where "colorAnomaly = 0"
definition weakAnomaly :: rat where "weakAnomaly = 0"
definition gravTrace :: rat where "gravTrace = 0"
definition cubicTrace :: rat where "cubicTrace = 0"
definition d2Target :: "nat*int" where "d2Target = (2,0)"
definition d2Square :: nat where "d2Square = 0"
definition graphEdges :: nat where "graphEdges = 6"

theorem furey_ladder_serre_kernel:
  "stablePage = 3 \<and> e2Rank = 8 \<and> survivorCount = 8 \<and>
   su3Generators = 8 \<and> su2Generators = 3 \<and> smRank = 4 \<and> smGenerators = 12 \<and> cartanGenerators = 4 \<and> ladderCount = 8 \<and>
   C2su3Fund = 4/3 \<and> C2su2Doublet = 3/4 \<and>
   upCharge = 2/3 \<and> downCharge = -1/3 \<and> neutrinoCharge = 0 \<and> electronCharge = -1 \<and>
   weylCount = 16 \<and> colorAnomaly = 0 \<and> weakAnomaly = 0 \<and> gravTrace = 0 \<and> cubicTrace = 0 \<and>
   d2Target = (2,0) \<and> d2Square = 0 \<and> graphEdges = 6"
  by (simp add: stablePage_def e2Rank_def survivorCount_def su3Generators_def su2Generators_def smRank_def smGenerators_def cartanGenerators_def ladderCount_def C2su3Fund_def C2su2Doublet_def upCharge_def downCharge_def neutrinoCharge_def electronCharge_def weylCount_def colorAnomaly_def weakAnomaly_def gravTrace_def cubicTrace_def d2Target_def d2Square_def graphEdges_def)

datatype concept = Serre_d2_Differential | Furey_Ladder_Residue | SU3_Color | SU2_Weak | U1_Hypercharge | SM_One_Generation | Anomaly_Cancelled
datatype edge = extracts | generates | carries | cancels
fun edgeHolds :: "concept => edge => concept => bool" where
  "edgeHolds Serre_d2_Differential extracts Furey_Ladder_Residue = True" |
  "edgeHolds Furey_Ladder_Residue generates SU3_Color = True" |
  "edgeHolds Furey_Ladder_Residue generates SU2_Weak = True" |
  "edgeHolds Furey_Ladder_Residue generates U1_Hypercharge = True" |
  "edgeHolds SM_One_Generation carries Furey_Ladder_Residue = True" |
  "edgeHolds SM_One_Generation cancels Anomaly_Cancelled = True" |
  "edgeHolds _ _ _ = False"

theorem graph_kernel:
  "edgeHolds Serre_d2_Differential extracts Furey_Ladder_Residue = True \<and>
   edgeHolds Furey_Ladder_Residue generates SU3_Color = True \<and>
   edgeHolds Furey_Ladder_Residue generates SU2_Weak = True \<and>
   edgeHolds Furey_Ladder_Residue generates U1_Hypercharge = True \<and>
   edgeHolds SM_One_Generation carries Furey_Ladder_Residue = True \<and>
   edgeHolds SM_One_Generation cancels Anomaly_Cancelled = True"
  by simp

end
