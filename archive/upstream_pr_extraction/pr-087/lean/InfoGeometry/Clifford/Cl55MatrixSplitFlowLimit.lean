import InfoGeometry.Clifford.Cl55SpinorAlgebraEquiv
import InfoGeometry.Clifford.Cl55WittProjectors
import InfoGeometry.Clifford.SplitFlowOperatorLimit

open Filter Topology

namespace InfoGeometry.Clifford.Cl55MatrixSplitFlowLimit

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.SpinorRep
open InfoGeometry.Clifford.SplitFlowOperatorLimit

noncomputable def matrixNormalizedSplitFlow (i : Fin 5) (t : ℝ) :
    SpinorMatrix 5 :=
  normalizedTwoLaneFlow
    (cl55SpinorAlgEquiv (hyperbolicProjector55Plus i))
    (cl55SpinorAlgEquiv (hyperbolicProjector55Minus i)) t

theorem matrixNormalizedSplitFlow_tendsto_atTop (i : Fin 5) :
    Tendsto (matrixNormalizedSplitFlow i) atTop
      (𝓝 (cl55SpinorAlgEquiv (hyperbolicProjector55Plus i))) := by
  exact normalizedTwoLaneFlow_tendsto_atTop
    (cl55SpinorAlgEquiv (hyperbolicProjector55Plus i))
    (cl55SpinorAlgEquiv (hyperbolicProjector55Minus i))

theorem matrixNormalizedSplitFlow_tendsto_atBot (i : Fin 5) :
    Tendsto (matrixNormalizedSplitFlow i) atBot
      (𝓝 (cl55SpinorAlgEquiv (hyperbolicProjector55Minus i))) := by
  exact normalizedTwoLaneFlow_tendsto_atBot
    (cl55SpinorAlgEquiv (hyperbolicProjector55Plus i))
    (cl55SpinorAlgEquiv (hyperbolicProjector55Minus i))

end InfoGeometry.Clifford.Cl55MatrixSplitFlowLimit
