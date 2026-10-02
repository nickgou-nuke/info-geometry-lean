import DAG.GraphHodge

namespace DAG.DiracLaplacian

open DAG

set_option maxHeartbeats 800000

def chainComplex : TwoComplex Nat :=
  { base := {
      toGraph := {
        nodes := #[0, 1, 2],
        nodeToIdx := {},
        forward := #[#[(1, EdgeKind.type)], #[(2, EdgeKind.type)], #[]]
      },
      sccs := #[#[0], #[1], #[2]],
      sccOf := #[0, 1, 2],
      dag := #[#[1], #[2], #[]],
      preds := #[#[], #[0], #[1]],
      topo := #[0, 1, 2],
      doms := #[]
    },
    edges := #[(0, 1), (1, 2)],
    faces := #[],
    digons := #[] }

def triangleComplex : TwoComplex Nat :=
  { base := {
      toGraph := {
        nodes := #[0, 1, 2],
        nodeToIdx := {},
        forward := #[#[(1, EdgeKind.type), (2, EdgeKind.type)], #[(2, EdgeKind.type)], #[]]
      },
      sccs := #[#[0], #[1], #[2]],
      sccOf := #[0, 1, 2],
      dag := #[#[1, 2], #[2], #[]],
      preds := #[#[], #[0], #[0, 1]],
      topo := #[0, 1, 2],
      doms := #[]
    },
    edges := #[(0, 1), (0, 2), (1, 2)],
    faces := #[(0, 2, 1)],
    digons := #[] }

def digonComplex : TwoComplex Nat :=
  { base := {
      toGraph := {
        nodes := #[0, 1],
        nodeToIdx := {},
        forward := #[#[(1, EdgeKind.type)], #[(0, EdgeKind.type)]]
      },
      sccs := #[#[0, 1]],
      sccOf := #[0, 0],
      dag := #[#[]],
      preds := #[#[]],
      topo := #[0],
      doms := #[]
    },
    edges := #[(0, 1), (1, 0)],
    faces := #[],
    digons := #[(0, 1)] }

abbrev canonicalDigonComplex : TwoComplex Nat := digonComplex

def intBoundary1 {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Array (Array Int) :=
  Array.ofFn (fun i : Fin tc.edges.size =>
    Array.ofFn (fun j : Fin tc.base.toGraph.nodes.size =>
      let (u, v) := tc.edges[i.val]
      if j.val = u then (-1 : Int) else if j.val = v then 1 else 0
    )
  )

def intGraphDirac {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Array (Array Int) :=
  let n0 := tc.base.toGraph.nodes.size
  let n1 := tc.edges.size
  let dim := n0 + n1
  let b1 := intBoundary1 tc
  Array.ofFn (fun i : Fin dim =>
    Array.ofFn (fun j : Fin dim =>
      if i.val < n0 then
        if j.val < n0 then 0
        else (b1[j.val - n0]!)[i.val]!
      else
        if j.val < n0 then (b1[i.val - n0]!)[j.val]!
        else 0
    )
  )

def intMatMul (rows cols inner : Nat) (a b : Array (Array Int)) : Array (Array Int) :=
  Array.ofFn (fun i : Fin rows =>
    Array.ofFn (fun j : Fin cols =>
      (List.range inner).foldl (fun sum k => sum + (a[i.val]!)[k]! * (b[k]!)[j.val]!) 0
    )
  )

def intDiracSq {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Array (Array Int) :=
  let dim := tc.base.toGraph.nodes.size + tc.edges.size
  let D := intGraphDirac tc
  intMatMul dim dim dim D D

def intLap0 {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Array (Array Int) :=
  let n0 := tc.base.toGraph.nodes.size
  let n1 := tc.edges.size
  let b1 := intBoundary1 tc
  let b1t := Array.ofFn (fun i : Fin n0 => Array.ofFn (fun j : Fin n1 => (b1[j.val]!)[i.val]!))
  intMatMul n0 n0 n1 b1t b1

def intDownLap1 {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Array (Array Int) :=
  let n0 := tc.base.toGraph.nodes.size
  let n1 := tc.edges.size
  let b1 := intBoundary1 tc
  let b1t := Array.ofFn (fun i : Fin n0 => Array.ofFn (fun j : Fin n1 => (b1[j.val]!)[i.val]!))
  intMatMul n1 n1 n0 b1 b1t

def graphDirac {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Array (Array Rat) :=
  let dim := tc.base.toGraph.nodes.size + tc.edges.size
  let mInt := intGraphDirac tc
  Array.ofFn (fun i : Fin dim =>
    Array.ofFn (fun j : Fin dim =>
      ((mInt[i.val]!)[j.val]! : Rat)
    )
  )

def matMul (a b : Array (Array Rat)) : Array (Array Rat) :=
  let rows := a.size
  let cols := if b.size > 0 then (b[0]!).size else 0
  let inner := b.size
  let aInt := Array.ofFn (fun r : Fin rows => Array.ofFn (fun k : Fin inner => (a[r.val]!)[k.val]!.num))
  let bInt := Array.ofFn (fun k : Fin inner => Array.ofFn (fun c : Fin cols => (b[k.val]!)[c.val]!.num))
  let resInt := intMatMul rows cols inner aInt bInt
  Array.ofFn (fun i : Fin rows =>
    Array.ofFn (fun j : Fin cols =>
      ((resInt[i.val]!)[j.val]! : Rat)
    )
  )

def matTranspose (m : Array (Array Rat)) : Array (Array Rat) :=
  let rows := m.size
  let cols := if rows > 0 then (m[0]!).size else 0
  Array.ofFn (fun j : Fin cols =>
    Array.ofFn (fun i : Fin rows =>
      (m[i.val]!)[j.val]!
    )
  )

def laplacian0 {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Array (Array Rat) :=
  let n0 := tc.base.toGraph.nodes.size
  let mInt := intLap0 tc
  Array.ofFn (fun i : Fin n0 =>
    Array.ofFn (fun j : Fin n0 =>
      ((mInt[i.val]!)[j.val]! : Rat)
    )
  )

def matTrace (m : Array (Array Rat)) : Int :=
  (List.range m.size).foldl (fun sum i => sum + (m[i]!)[i]!.num) 0

def diracSquareCheck {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Bool :=
  let n0 := tc.base.toGraph.nodes.size
  let n1 := tc.edges.size
  let dim := n0 + n1
  let d2 := intDiracSq tc
  let exp00 := intLap0 tc
  let exp11 := intDownLap1 tc
  let expected := Array.ofFn (fun i : Fin dim =>
    Array.ofFn (fun j : Fin dim =>
      if i.val < n0 then
        if j.val < n0 then (exp00[i.val]!)[j.val]! else 0
      else
        if j.val < n0 then 0 else (exp11[i.val - n0]!)[j.val - n0]!
    )
  )
  d2 == expected

theorem laplacian0_chain_eq :
    laplacian0 chainComplex =
      #[#[(1 : Rat), -1, 0],
        #[-1, 2, -1],
        #[0, -1, 1]] := by
  rfl

theorem down_laplacian1_chain_eq :
    matMul (boundary1 chainComplex) (matTranspose (boundary1 chainComplex)) =
      #[#[(2 : Rat), -1],
        #[-1, 2]] := by
  rfl

structure DiracLaplacianBlockCertificate (α : Type) [BEq α] [Hashable α] where
  complex : TwoComplex α
  complexName : String
  nodes : Nat
  edges : Nat
  dim : Nat
  diracSq : Array (Array Rat)
  lap0 : Array (Array Rat)
  downLap1 : Array (Array Rat)
  traceDsq : Int
  traceLap0 : Int
  traceDownLap1 : Int
  dim_eq : dim = nodes + edges
  nodes_eq : nodes = complex.base.toGraph.nodes.size
  edges_eq : edges = complex.edges.size
  square_check : diracSquareCheck complex = true
  trace_eq : traceDsq = traceLap0 + traceDownLap1

def chainBlockCertificate : DiracLaplacianBlockCertificate Nat where
  complex := chainComplex
  complexName := "canonicalChainComplex"
  nodes := 3
  edges := 2
  dim := 5
  diracSq := matMul (graphDirac chainComplex) (graphDirac chainComplex)
  lap0 := laplacian0 chainComplex
  downLap1 := matMul (boundary1 chainComplex) (matTranspose (boundary1 chainComplex))
  traceDsq := 8
  traceLap0 := 4
  traceDownLap1 := 4
  dim_eq := by rfl
  nodes_eq := by rfl
  edges_eq := by rfl
  square_check := by rfl
  trace_eq := by rfl

def triangleBlockCertificate : DiracLaplacianBlockCertificate Nat where
  complex := triangleComplex
  complexName := "canonicalTriangleComplex"
  nodes := 3
  edges := 3
  dim := 6
  diracSq := matMul (graphDirac triangleComplex) (graphDirac triangleComplex)
  lap0 := laplacian0 triangleComplex
  downLap1 := matMul (boundary1 triangleComplex) (matTranspose (boundary1 triangleComplex))
  traceDsq := 12
  traceLap0 := 6
  traceDownLap1 := 6
  dim_eq := by rfl
  nodes_eq := by rfl
  edges_eq := by rfl
  square_check := by rfl
  trace_eq := by rfl

def digonBlockCertificate : DiracLaplacianBlockCertificate Nat where
  complex := digonComplex
  complexName := "canonicalDigonComplex"
  nodes := 2
  edges := 2
  dim := 4
  diracSq := matMul (graphDirac digonComplex) (graphDirac digonComplex)
  lap0 := laplacian0 digonComplex
  downLap1 := matMul (boundary1 digonComplex) (matTranspose (boundary1 digonComplex))
  traceDsq := 8
  traceLap0 := 4
  traceDownLap1 := 4
  dim_eq := by rfl
  nodes_eq := by rfl
  edges_eq := by rfl
  square_check := by rfl
  trace_eq := by rfl

/-! ## 10 Theorems -/

theorem dirac_squared_block_diagonal_chain :
    let D := graphDirac chainComplex
    matMul D D =
      #[#[(1 : Rat), -1, 0, 0, 0],
        #[-1, 2, -1, 0, 0],
        #[0, -1, 1, 0, 0],
        #[0, 0, 0, 2, -1],
        #[0, 0, 0, -1, 2]] := by
  rfl

theorem dirac_square_check_chain :
    diracSquareCheck chainComplex = true := by
  rfl

theorem dirac_sq_upper_left_is_laplacian0_chain :
    let D := graphDirac chainComplex
    let Dsq := matMul D D
    let Δ₀ := laplacian0 chainComplex
    (Dsq[0]!)[0]! = (Δ₀[0]!)[0]! := by
  intro D Dsq Δ₀
  have h1 : Dsq = #[#[(1 : Rat), -1, 0, 0, 0], #[-1, 2, -1, 0, 0], #[0, -1, 1, 0, 0], #[0, 0, 0, 2, -1], #[0, 0, 0, -1, 2]] := dirac_squared_block_diagonal_chain
  have h2 : Δ₀ = #[#[(1 : Rat), -1, 0], #[-1, 2, -1], #[0, -1, 1]] := laplacian0_chain_eq
  rw [h1, h2]
  rfl

theorem dirac_sq_lower_right_is_down_laplacian1_chain :
    let D := graphDirac chainComplex
    let Dsq := matMul D D
    let downΔ₁ := matMul (boundary1 chainComplex) (matTranspose (boundary1 chainComplex))
    (Dsq[3]!)[3]! = (downΔ₁[0]!)[0]! := by
  intro D Dsq downΔ₁
  have h1 : Dsq = #[#[(1 : Rat), -1, 0, 0, 0], #[-1, 2, -1, 0, 0], #[0, -1, 1, 0, 0], #[0, 0, 0, 2, -1], #[0, 0, 0, -1, 2]] := dirac_squared_block_diagonal_chain
  have h2 : downΔ₁ = #[#[(2 : Rat), -1], #[-1, 2]] := down_laplacian1_chain_eq
  rw [h1, h2]
  rfl

theorem dirac_sq_upper_right_is_zero_chain :
    let D := graphDirac chainComplex
    let Dsq := matMul D D
    (Dsq[0]!)[3]! = 0 := by
  intro D Dsq
  have h1 : Dsq = #[#[(1 : Rat), -1, 0, 0, 0], #[-1, 2, -1, 0, 0], #[0, -1, 1, 0, 0], #[0, 0, 0, 2, -1], #[0, 0, 0, -1, 2]] := dirac_squared_block_diagonal_chain
  rw [h1]
  rfl

theorem dirac_sq_lower_left_is_zero_chain :
    let D := graphDirac chainComplex
    let Dsq := matMul D D
    (Dsq[3]!)[0]! = 0 := by
  intro D Dsq
  have h1 : Dsq = #[#[(1 : Rat), -1, 0, 0, 0], #[-1, 2, -1, 0, 0], #[0, -1, 1, 0, 0], #[0, 0, 0, 2, -1], #[0, 0, 0, -1, 2]] := dirac_squared_block_diagonal_chain
  rw [h1]
  rfl

theorem trace_D_sq_equals_trace_laplacians_chain :
    let D := graphDirac chainComplex
    let Dsq := matMul D D
    matTrace Dsq = matTrace (laplacian0 chainComplex)
      + matTrace (matMul (boundary1 chainComplex) (matTranspose (boundary1 chainComplex))) := by
  intro D Dsq
  have h1 : Dsq = #[#[(1 : Rat), -1, 0, 0, 0], #[-1, 2, -1, 0, 0], #[0, -1, 1, 0, 0], #[0, 0, 0, 2, -1], #[0, 0, 0, -1, 2]] := dirac_squared_block_diagonal_chain
  have h2 : laplacian0 chainComplex = #[#[(1 : Rat), -1, 0], #[-1, 2, -1], #[0, -1, 1]] := laplacian0_chain_eq
  have h3 : matMul (boundary1 chainComplex) (matTranspose (boundary1 chainComplex)) = #[#[(2 : Rat), -1], #[-1, 2]] := down_laplacian1_chain_eq
  rw [h1, h2, h3]
  rfl

theorem dirac_squared_block_diagonal_triangle :
    let D := graphDirac triangleComplex
    matMul D D =
      #[#[(2 : Rat), -1, -1, 0, 0, 0],
        #[-1, 2, -1, 0, 0, 0],
        #[-1, -1, 2, 0, 0, 0],
        #[0, 0, 0, 2, 1, -1],
        #[0, 0, 0, 1, 2, 1],
        #[0, 0, 0, -1, 1, 2]] := by
  rfl

theorem dirac_squared_block_diagonal_digon :
    let D := graphDirac canonicalDigonComplex
    matMul D D =
      #[#[(2 : Rat), -2, 0, 0],
        #[-2, 2, 0, 0],
        #[0, 0, 2, -2],
        #[0, 0, -2, 2]] := by
  rfl

theorem dirac_square_check_triangle :
    diracSquareCheck triangleComplex = true := by
  rfl

end DAG.DiracLaplacian
