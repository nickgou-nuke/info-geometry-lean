import DAG.Algo.All

/-!
# DAG.Algo.Smoke

Tiny executable smoke checks for the generic graph algorithm layer.
-/

#eval DAG.Algo.edgeCount (#[#[1, 2], #[2], #[]] : DAG.Algo.Adj)
#eval DAG.Algo.inDegrees (#[#[1, 2], #[2], #[]] : DAG.Algo.Adj)
#eval DAG.Algo.reverseAdj (#[#[1, 2], #[2], #[]] : DAG.Algo.Adj)
#eval DAG.Algo.bfsDistances (#[#[1], #[2], #[]] : DAG.Algo.Adj) 0
#eval DAG.Algo.checkAdjBounds (#[#[1, 2], #[2], #[]] : DAG.Algo.Adj)
#eval DAG.Algo.checkReverseAdj
  (#[#[1, 2], #[2], #[]] : DAG.Algo.Adj)
  (#[#[], #[0], #[0, 1]] : DAG.Algo.Adj)
#eval DAG.Algo.checkBfsParents
  (#[#[1], #[2], #[]] : DAG.Algo.Adj)
  0
  (DAG.Algo.bfsTreeParents (#[#[1], #[2], #[]] : DAG.Algo.Adj) 0)
#eval DAG.Algo.checkTopoOrder
  (#[#[1, 2], #[2], #[]] : DAG.Algo.Adj)
  #[0, 1, 2]
