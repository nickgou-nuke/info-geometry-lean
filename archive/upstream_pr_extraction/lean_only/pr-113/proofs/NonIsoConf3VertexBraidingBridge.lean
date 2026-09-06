import proofs.VertexAlgebraBraidingCocycle
import proofs.NonIsoConf3BraidedCocycleEntropy
import proofs.BraidedCocycleWilsonEntropy

noncomputable section
namespace NonIsoConf3VertexBraidingBridge

open VertexAlgebraBraidingCocycle
open VertexAlgebraBraidingCocycle.EdgeSystem

abbrev Conf3Vertex := Fin 3

def conf3TriangleCycle : SpinNetCycle Conf3Vertex where
  start := 0
  interior := [1, 2]

/-- The affinity of the 3-point cycle explicitly expands to the sum of 
its three directed edge log-ratios. This reveals the true geometry of the 
braiding cycle over Conf_3. -/
theorem conf3TriangleCycle_affinity_formula (S : EdgeSystem Conf3Vertex) :
    cycleAffinity S conf3TriangleCycle = 
    logRatio S 0 1 + logRatio S 1 2 + logRatio S 2 0 := by
  dsimp [conf3TriangleCycle, cycleAffinity, cycleWalk]
  abel

theorem conf3_vertex_braiding_bridge_synthesis (S : EdgeSystem Conf3Vertex) : 
    cycleAffinity S conf3TriangleCycle = 
    logRatio S 0 1 + logRatio S 1 2 + logRatio S 2 0 := conf3TriangleCycle_affinity_formula S

end NonIsoConf3VertexBraidingBridge
end noncomputable section
