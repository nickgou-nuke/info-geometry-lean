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

/-- The canonical chain has zero boundary composition explicitly. -/
theorem boundary2_mul_boundary1_chain :
    matMul (boundary2 canonicalChainComplex) (boundary1 canonicalChainComplex) =
      #[] := by
  native_decide

theorem boundary_squared_zero_triangle :
    boundarySquaredZero canonicalTriangleComplex = true := by
  native_decide

/-- The actual boundary composition vanishes on the canonical triangle. -/
theorem boundary2_mul_boundary1_triangle :
    matMul (boundary2 canonicalTriangleComplex) (boundary1 canonicalTriangleComplex) =
      #[#[0, 0, 0]] := by
  native_decide

/-- The canonical triangle 0-Laplacian is the standard `K₃` graph Laplacian. -/
theorem laplacian0_triangle_matrix :
    laplacian0 canonicalTriangleComplex =
      #[#[(2 : Rat), -1, -1],
        #[-1, 2, -1],
        #[-1, -1, 2]] := by
  native_decide

/-- The canonical triangle 1-Laplacian is the scalar matrix `3 I`. -/
theorem laplacian1_triangle_matrix :
    laplacian1 canonicalTriangleComplex =
      #[#[(3 : Rat), 0, 0],
        #[0, 3, 0],
        #[0, 0, 3]] := by
  native_decide

theorem boundary_squared_zero_digon :
    boundarySquaredZero canonicalDigonComplex = true := by
  native_decide

/-- The digon boundary composition vanishes explicitly. -/
theorem boundary2_mul_boundary1_digon :
    matMul (boundary2 canonicalDigonComplex) (boundary1 canonicalDigonComplex) =
      #[#[0, 0]] := by
  native_decide

/-! ## Laplacian Self-Adjointness Checks -/

theorem laplacian0_self_adjoint_chain :
    laplacian0SelfAdjointCheck canonicalChainComplex = true := by
  native_decide

theorem laplacian1_self_adjoint_chain :
    laplacian1SelfAdjointCheck canonicalChainComplex = true := by
  native_decide

/-- Canonical chain vertex Laplacian is explicitly symmetric. -/
theorem laplacian0_chain_self_adjoint :
    matTranspose (laplacian0 canonicalChainComplex) =
      laplacian0 canonicalChainComplex := by
  native_decide

/-- Canonical chain 1-Laplacian is explicitly symmetric. -/
theorem laplacian1_chain_self_adjoint :
    matTranspose (laplacian1 canonicalChainComplex) =
      laplacian1 canonicalChainComplex := by
  native_decide

/-- The canonical chain 0-Laplacian is the path-graph Laplacian. -/
theorem laplacian0_chain_matrix :
    laplacian0 canonicalChainComplex =
      #[#[(1 : Rat), -1, 0],
        #[-1, 2, -1],
        #[0, -1, 1]] := by
  native_decide

/-- The canonical chain 1-Laplacian is the `2×2` path-edge Laplacian. -/
theorem laplacian1_chain_matrix :
    laplacian1 canonicalChainComplex =
      #[#[(2 : Rat), -1],
        #[-1, 2]] := by
  native_decide

theorem laplacian0_self_adjoint_triangle :
    laplacian0SelfAdjointCheck canonicalTriangleComplex = true := by
  native_decide

theorem laplacian1_self_adjoint_triangle :
    laplacian1SelfAdjointCheck canonicalTriangleComplex = true := by
  native_decide

/-- Canonical triangle vertex Laplacian is explicitly symmetric. -/
theorem laplacian0_triangle_self_adjoint :
    matTranspose (laplacian0 canonicalTriangleComplex) =
      laplacian0 canonicalTriangleComplex := by
  native_decide

/-- Canonical triangle 1-Laplacian is explicitly symmetric. -/
theorem laplacian1_triangle_self_adjoint :
    matTranspose (laplacian1 canonicalTriangleComplex) =
      laplacian1 canonicalTriangleComplex := by
  native_decide

/-- Canonical digon vertex Laplacian is explicitly symmetric. -/
theorem laplacian0_digon_matrix :
    laplacian0 canonicalDigonComplex =
      #[#[(2 : Rat), -2],
        #[-2, 2]] := by
  native_decide

/-- Canonical digon 1-Laplacian is explicitly symmetric. -/
theorem laplacian1_digon_matrix :
    laplacian1 canonicalDigonComplex =
      #[#[(3 : Rat), -1],
        #[-1, 3]] := by
  native_decide

/-- Canonical digon vertex Laplacian is explicitly symmetric. -/
theorem laplacian0_digon_self_adjoint :
    matTranspose (laplacian0 canonicalDigonComplex) =
      laplacian0 canonicalDigonComplex := by
  native_decide

/-- Canonical digon 1-Laplacian is explicitly symmetric. -/
theorem laplacian1_digon_self_adjoint :
    matTranspose (laplacian1 canonicalDigonComplex) =
      laplacian1 canonicalDigonComplex := by
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

/-- The canonical digon Betti number agrees with the Hodge computation. -/
theorem betti1_agrees_with_hodge_digon :
    (betti1 canonicalDigonComplex).toNat = betti1Hodge canonicalDigonComplex := by
  native_decide

theorem betti1_zero_triangle :
    betti1 canonicalTriangleComplex = 0 := by
  native_decide

/-- The canonical chain has vanishing first Betti number. -/
theorem betti1_zero_chain :
    betti1 canonicalChainComplex = 0 := by
  native_decide

/-- The canonical digon has vanishing first Betti number. -/
theorem betti1_zero_digon :
    betti1 canonicalDigonComplex = 0 := by
  native_decide

/-- Digon rank identity: the rank sum equals the number of edges. -/
theorem betti1_rank_identity_digon :
    (betti1 canonicalDigonComplex).toNat + gaussianRank (boundary1 canonicalDigonComplex) +
        gaussianRank (boundary2 canonicalDigonComplex) =
      canonicalDigonComplex.edges.size := by
  native_decide

/-- Digon Euler characteristic equals the alternating Betti sum. -/
theorem euler_equals_betti_alternating_sum_digon :
    eulerCharacteristic canonicalDigonComplex =
      (betti0 canonicalDigonComplex : Int) - betti1 canonicalDigonComplex := by
  native_decide

theorem dirac_dimension_chain :
    (hodgeSummary canonicalChainComplex).diracDim = 5 := by
  native_decide

/-- The canonical triangle Dirac dimension is `6`. -/
theorem dirac_dimension_triangle :
    (hodgeSummary canonicalTriangleComplex).diracDim = 6 := by
  native_decide

/-- The canonical digon Dirac dimension is `4`. -/
theorem dirac_dimension_digon :
    (hodgeSummary canonicalDigonComplex).diracDim = 4 := by
  native_decide

/-- The full canonical chain Hodge summary. -/
theorem hodge_summary_chain :
    hodgeSummary canonicalChainComplex =
      { nodes := 3, edges := 2, faces := 0, euler := 1, b0 := 1, b1 := 0,
        b1Hodge := 0, traceΔ0 := 4, diracDim := 5 } := by
  native_decide

/-- The full canonical triangle Hodge summary. -/
theorem hodge_summary_triangle :
    hodgeSummary canonicalTriangleComplex =
      { nodes := 3, edges := 3, faces := 1, euler := 1, b0 := 1, b1 := 0,
        b1Hodge := 0, traceΔ0 := 6, diracDim := 6 } := by
  native_decide

/-- The full canonical digon Hodge summary. -/
theorem hodge_summary_digon :
    hodgeSummary canonicalDigonComplex =
      { nodes := 2, edges := 2, faces := 1, euler := 1, b0 := 1, b1 := 0,
        b1Hodge := 0, traceΔ0 := 4, diracDim := 4 } := by
  native_decide

/-! ## Chiral Compatibility Checks -/

def constantPlusChainGrading : ChiralGrading canonicalChainComplex.base.toGraph.nodes.size :=
  ChiralGrading.ofBool canonicalChainComplex.base.toGraph.nodes.size (fun _ => true)

def constantPlusTriangleGrading : ChiralGrading canonicalTriangleComplex.base.toGraph.nodes.size :=
  ChiralGrading.ofBool canonicalTriangleComplex.base.toGraph.nodes.size (fun _ => true)

theorem chiral_anticommutes_constant_chain :
    chiralAnticommutes canonicalChainComplex constantPlusChainGrading = true := by
  native_decide

/-- The canonical chain grading matrix is the identity on vertices and minus identity on edges. -/
theorem extended_chiral_grading_chain_matrix :
    extendedChiralGrading canonicalChainComplex constantPlusChainGrading =
      #[#[(1 : Rat), 0, 0, 0, 0],
        #[0, 1, 0, 0, 0],
        #[0, 0, 1, 0, 0],
        #[0, 0, 0, -1, 0],
        #[0, 0, 0, 0, -1]] := by
  native_decide

/-- The canonical chain Dirac operator anticommutes with the canonical grading. -/
theorem chiral_anticommutator_zero_chain :
    matAdd
      (matMul (extendedChiralGrading canonicalChainComplex constantPlusChainGrading)
        (graphDirac canonicalChainComplex))
      (matMul (graphDirac canonicalChainComplex)
        (extendedChiralGrading canonicalChainComplex constantPlusChainGrading)) =
      #[
        #[0, 0, 0, 0, 0],
        #[0, 0, 0, 0, 0],
        #[0, 0, 0, 0, 0],
        #[0, 0, 0, 0, 0],
        #[0, 0, 0, 0, 0]
      ] := by
  native_decide

theorem chiral_anticommutes_constant_triangle :
    chiralAnticommutes canonicalTriangleComplex constantPlusTriangleGrading = true := by
  native_decide

/-- The canonical triangle grading matrix is the identity on vertices and minus identity on edges. -/
theorem extended_chiral_grading_triangle_matrix :
    extendedChiralGrading canonicalTriangleComplex constantPlusTriangleGrading =
      #[#[(1 : Rat), 0, 0, 0, 0, 0],
        #[0, 1, 0, 0, 0, 0],
        #[0, 0, 1, 0, 0, 0],
        #[0, 0, 0, -1, 0, 0],
        #[0, 0, 0, 0, -1, 0],
        #[0, 0, 0, 0, 0, -1]] := by
  native_decide

/-- The canonical triangle Dirac operator anticommutes with the canonical grading. -/
theorem chiral_anticommutator_zero_triangle :
    matAdd
      (matMul (extendedChiralGrading canonicalTriangleComplex constantPlusTriangleGrading)
        (graphDirac canonicalTriangleComplex))
      (matMul (graphDirac canonicalTriangleComplex)
        (extendedChiralGrading canonicalTriangleComplex constantPlusTriangleGrading)) =
      #[
        #[0, 0, 0, 0, 0, 0],
        #[0, 0, 0, 0, 0, 0],
        #[0, 0, 0, 0, 0, 0],
        #[0, 0, 0, 0, 0, 0],
        #[0, 0, 0, 0, 0, 0],
        #[0, 0, 0, 0, 0, 0]
      ] := by
  native_decide

/-! ## Exported Boolean Checks -/

theorem dirac_square_check_chain :
    diracSquareCheck canonicalChainComplex = true := by
  native_decide

/-- Exported compatibility check for downstream code that expects a boolean gate. -/
theorem dirac_square_check_triangle :
    diracSquareCheck canonicalTriangleComplex = true := by
  native_decide

end DAG
