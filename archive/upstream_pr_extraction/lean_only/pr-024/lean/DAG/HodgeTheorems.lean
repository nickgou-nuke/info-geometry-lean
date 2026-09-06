import DAG.TwoComplex
import DAG.GraphHodge

/-!
# DAG.HodgeTheorems

Concrete finite checks for the DAG two-complex Hodge layer.

The general operator identities live as executable matrix constructions in
`DAG.TwoComplex` and `DAG.GraphHodge`. This file records small canonical
instances as kernel-checked `native_decide` theorems, so downstream bridge
files can point at real checked owner declarations rather than comments.
-/

namespace DAG

/-! ## Canonical Small Graphs -/

/-- Chain graph `0 → 1 → 2`. -/
def canonicalChain : HydratedGraph Nat := Id.run do
  let nodes : Array Nat := #[0, 1, 2]
  let mut nodeToIdx : Std.HashMap Nat Nat := {}
  for i in [:3] do
    nodeToIdx := nodeToIdx.insert nodes[i]! i
  let forward : Array (Array (Nat × EdgeKind)) := #[
    #[(1, EdgeKind.type)],
    #[(2, EdgeKind.type)],
    #[]
  ]
  { toGraph := { nodes := nodes, nodeToIdx := nodeToIdx, forward := forward }
    sccs := #[#[0], #[1], #[2]]
    sccOf := #[0, 1, 2]
    dag := #[#[1], #[2], #[]]
    preds := #[#[], #[0], #[1]]
    topo := #[0, 1, 2]
    doms := #[] }

/-- Triangle graph `0 → 1`, `1 → 2`, `0 → 2`. -/
def canonicalTriangle : HydratedGraph Nat := Id.run do
  let nodes : Array Nat := #[0, 1, 2]
  let mut nodeToIdx : Std.HashMap Nat Nat := {}
  for i in [:3] do
    nodeToIdx := nodeToIdx.insert nodes[i]! i
  let forward : Array (Array (Nat × EdgeKind)) := #[
    #[(1, EdgeKind.type), (2, EdgeKind.type)],
    #[(2, EdgeKind.type)],
    #[]
  ]
  { toGraph := { nodes := nodes, nodeToIdx := nodeToIdx, forward := forward }
    sccs := #[#[0], #[1], #[2]]
    sccOf := #[0, 1, 2]
    dag := #[#[1, 2], #[2], #[]]
    preds := #[#[], #[0], #[0, 1]]
    topo := #[0, 1, 2]
    doms := #[] }

/-- Digon graph `0 ⇄ 1`. -/
def canonicalDigon : HydratedGraph Nat := Id.run do
  let nodes : Array Nat := #[0, 1]
  let mut nodeToIdx : Std.HashMap Nat Nat := {}
  for i in [:2] do
    nodeToIdx := nodeToIdx.insert nodes[i]! i
  let forward : Array (Array (Nat × EdgeKind)) := #[
    #[(1, EdgeKind.type)],
    #[(0, EdgeKind.type)]
  ]
  { toGraph := { nodes := nodes, nodeToIdx := nodeToIdx, forward := forward }
    sccs := #[#[0, 1]]
    sccOf := #[0, 0]
    dag := #[#[]]
    preds := #[#[]]
    topo := #[0]
    doms := #[] }

def canonicalChainComplex : TwoComplex Nat :=
  buildTwoComplex canonicalChain

def canonicalTriangleComplex : TwoComplex Nat :=
  buildTwoComplex canonicalTriangle

def canonicalDigonComplex : TwoComplex Nat :=
  buildTwoComplex canonicalDigon

/-! ## Boundary-Squared-Zero Checks -/

theorem boundary_squared_zero_chain :
    boundarySquaredZero canonicalChainComplex = true := by
  native_decide

theorem boundary_squared_zero_triangle :
    boundarySquaredZero canonicalTriangleComplex = true := by
  native_decide

theorem boundary_squared_zero_digon :
    boundarySquaredZero canonicalDigonComplex = true := by
  native_decide

/-! ## Laplacian Self-Adjointness Checks -/

theorem laplacian0_self_adjoint_chain :
    laplacian0SelfAdjointCheck canonicalChainComplex = true := by
  native_decide

theorem laplacian1_self_adjoint_chain :
    laplacian1SelfAdjointCheck canonicalChainComplex = true := by
  native_decide

theorem laplacian0_self_adjoint_triangle :
    laplacian0SelfAdjointCheck canonicalTriangleComplex = true := by
  native_decide

theorem laplacian1_self_adjoint_triangle :
    laplacian1SelfAdjointCheck canonicalTriangleComplex = true := by
  native_decide

/-! ## Betti, Hodge, And Euler Checks -/

theorem betti1_rank_identity_chain :
    (betti1 canonicalChainComplex).toNat + gaussianRank (boundary1 canonicalChainComplex) +
        gaussianRank (boundary2 canonicalChainComplex) =
      canonicalChainComplex.edges.size := by
  native_decide

theorem betti1_rank_identity_triangle :
    (betti1 canonicalTriangleComplex).toNat + gaussianRank (boundary1 canonicalTriangleComplex) +
        gaussianRank (boundary2 canonicalTriangleComplex) =
      canonicalTriangleComplex.edges.size := by
  native_decide

theorem euler_equals_betti_alternating_sum_chain :
    eulerCharacteristic canonicalChainComplex =
      (betti0 canonicalChainComplex : Int) - betti1 canonicalChainComplex := by
  native_decide

theorem euler_equals_betti_alternating_sum_triangle :
    eulerCharacteristic canonicalTriangleComplex =
      (betti0 canonicalTriangleComplex : Int) - betti1 canonicalTriangleComplex := by
  native_decide

theorem betti1_agrees_with_hodge_chain :
    (betti1 canonicalChainComplex).toNat = betti1Hodge canonicalChainComplex := by
  native_decide

theorem betti1_agrees_with_hodge_triangle :
    (betti1 canonicalTriangleComplex).toNat = betti1Hodge canonicalTriangleComplex := by
  native_decide

theorem dirac_dimension_chain :
    (hodgeSummary canonicalChainComplex).diracDim = 5 := by
  native_decide

/-! ## Chiral Compatibility Checks -/

def constantPlusChainGrading : ChiralGrading canonicalChainComplex.base.toGraph.nodes.size :=
  ChiralGrading.ofBool canonicalChainComplex.base.toGraph.nodes.size (fun _ => true)

def constantPlusTriangleGrading : ChiralGrading canonicalTriangleComplex.base.toGraph.nodes.size :=
  ChiralGrading.ofBool canonicalTriangleComplex.base.toGraph.nodes.size (fun _ => true)

theorem chiral_anticommutes_constant_chain :
    chiralAnticommutes canonicalChainComplex constantPlusChainGrading = true := by
  native_decide

theorem chiral_anticommutes_constant_triangle :
    chiralAnticommutes canonicalTriangleComplex constantPlusTriangleGrading = true := by
  native_decide

/-! ## Exported Boolean Checks -/

theorem dirac_square_check_chain :
    diracSquareCheck canonicalChainComplex = true := by
  native_decide

end DAG
