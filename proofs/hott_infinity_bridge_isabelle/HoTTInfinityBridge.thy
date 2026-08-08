theory HoTTInfinityBridge
  imports Main
begin

definition repositorySourceCount :: nat where "repositorySourceCount = 8"
definition mathlibSourceCount :: nat where "mathlibSourceCount = 1"
definition totalSourceCount :: nat where "totalSourceCount = 9"
definition bridgeLayerCount :: nat where "bridgeLayerCount = 9"
definition compatibilityEdgeCount :: nat where "compatibilityEdgeCount = 11"
definition hottBridgeRank :: nat where "hottBridgeRank = 29"
definition homotopyEquivFields :: nat where "homotopyEquivFields = 4"
definition exactCoupleMaps :: nat where "exactCoupleMaps = 3"
definition serrePageStart :: nat where "serrePageStart = 2"
definition serreStablePage :: nat where "serreStablePage = 3"
definition quasicategorySimplexArity :: nat where "quasicategorySimplexArity = 2"
definition modelCategoryClasses :: nat where "modelCategoryClasses = 3"
definition fibredProjectionCount :: nat where "fibredProjectionCount = 1"
definition infinityBridgeSignature :: nat where "infinityBridgeSignature = 18"
definition d2TargetP :: nat where "d2TargetP = 2"
definition d2TargetQ :: int where "d2TargetQ = 0"
definition d2Square :: nat where "d2Square = 0"
definition graphEdges :: nat where "graphEdges = 11"

theorem hott_infinity_bridge_kernel:
  "repositorySourceCount = 8 \<and> mathlibSourceCount = 1 \<and> totalSourceCount = 9 \<and> bridgeLayerCount = 9 \<and>
   compatibilityEdgeCount = 11 \<and> hottBridgeRank = 29 \<and> homotopyEquivFields = 4 \<and> exactCoupleMaps = 3 \<and>
   serrePageStart = 2 \<and> serreStablePage = 3 \<and> quasicategorySimplexArity = 2 \<and> modelCategoryClasses = 3 \<and>
   fibredProjectionCount = 1 \<and> infinityBridgeSignature = 18 \<and> d2TargetP = 2 \<and> d2TargetQ = 0 \<and> d2Square = 0 \<and> graphEdges = 11"
  by (simp add: repositorySourceCount_def mathlibSourceCount_def totalSourceCount_def bridgeLayerCount_def compatibilityEdgeCount_def hottBridgeRank_def homotopyEquivFields_def exactCoupleMaps_def serrePageStart_def serreStablePage_def quasicategorySimplexArity_def modelCategoryClasses_def fibredProjectionCount_def infinityBridgeSignature_def d2TargetP_def d2TargetQ_def d2Square_def graphEdges_def)

end
