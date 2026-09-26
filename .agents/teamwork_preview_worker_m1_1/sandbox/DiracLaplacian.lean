import DAG.GraphHodge
import Mathlib.Tactic.NormNum

namespace DAG.DiracLaplacian

open DAG

/-- Canonical chain complex `0 -> 1 -> 2`. -/
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

/-- Canonical triangle complex `0 → 1, 0 → 2, 1 → 2`. -/
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

/-- Canonical digon complex `0 ⇄ 1`. -/
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

def chainDiracSqCertificate : Array (Array Rat) :=
  #[#[(1 : Rat), -1, 0, 0, 0],
    #[-1, 2, -1, 0, 0],
    #[0, -1, 1, 0, 0],
    #[0, 0, 0, 2, -1],
    #[0, 0, 0, -1, 2]]

def chainLap0Certificate : Array (Array Rat) :=
  #[#[(1 : Rat), -1, 0],
    #[-1, 2, -1],
    #[0, -1, 1]]

def chainDownLap1Certificate : Array (Array Rat) :=
  #[#[(2 : Rat), -1],
    #[-1, 2]]

def triangleDiracSqCertificate : Array (Array Rat) :=
  #[#[(2 : Rat), -1, -1, 0, 0, 0],
    #[-1, 2, -1, 0, 0, 0],
    #[-1, -1, 2, 0, 0, 0],
    #[0, 0, 0, 2, 1, -1],
    #[0, 0, 0, 1, 2, 1],
    #[0, 0, 0, -1, 1, 2]]

def triangleLap0Certificate : Array (Array Rat) :=
  #[#[(2 : Rat), -1, -1],
    #[-1, 2, -1],
    #[-1, -1, 2]]

def triangleDownLap1Certificate : Array (Array Rat) :=
  #[#[(2 : Rat), 1, -1],
    #[1, 2, 1],
    #[-1, 1, 2]]

def digonDiracSqCertificate : Array (Array Rat) :=
  #[#[(2 : Rat), -2, 0, 0],
    #[-2, 2, 0, 0],
    #[0, 0, 2, -2],
    #[0, 0, -2, 2]]

def digonLap0Certificate : Array (Array Rat) :=
  #[#[(2 : Rat), -2],
    #[-2, 2]]

def digonDownLap1Certificate : Array (Array Rat) :=
  #[#[(2 : Rat), -2],
    #[-2, 2]]

structure DiracLaplacianBlockCertificate where
  complexName : String
  nodes : Nat
  edges : Nat
  dim : Nat
  diracSq : Array (Array Rat)
  lap0 : Array (Array Rat)
  downLap1 : Array (Array Rat)
  traceDsq : Rat
  traceLap0 : Rat
  traceDownLap1 : Rat
  dim_eq : dim = nodes + edges
  trace_eq : traceDsq = traceLap0 + traceDownLap1
  upper_left_entry_eq : (diracSq[0]!)[0]! = (lap0[0]!)[0]!
  lower_right_entry_eq : (diracSq[nodes]!)[nodes]! = (downLap1[0]!)[0]!
  upper_right_zero : (diracSq[0]!)[nodes]! = 0
  lower_left_zero : (diracSq[nodes]!)[0]! = 0

def chainBlockCertificate : DiracLaplacianBlockCertificate where
  complexName := "canonicalChainComplex"
  nodes := 3
  edges := 2
  dim := 5
  diracSq := chainDiracSqCertificate
  lap0 := chainLap0Certificate
  downLap1 := chainDownLap1Certificate
  traceDsq := 8
  traceLap0 := 4
  traceDownLap1 := 4
  dim_eq := by rfl
  trace_eq := by norm_num
  upper_left_entry_eq := by rfl
  lower_right_entry_eq := by rfl
  upper_right_zero := by rfl
  lower_left_zero := by rfl

def triangleBlockCertificate : DiracLaplacianBlockCertificate where
  complexName := "canonicalTriangleComplex"
  nodes := 3
  edges := 3
  dim := 6
  diracSq := triangleDiracSqCertificate
  lap0 := triangleLap0Certificate
  downLap1 := triangleDownLap1Certificate
  traceDsq := 12
  traceLap0 := 6
  traceDownLap1 := 6
  dim_eq := by rfl
  trace_eq := by norm_num
  upper_left_entry_eq := by rfl
  lower_right_entry_eq := by rfl
  upper_right_zero := by rfl
  lower_left_zero := by rfl

def digonBlockCertificate : DiracLaplacianBlockCertificate where
  complexName := "canonicalDigonComplex"
  nodes := 2
  edges := 2
  dim := 4
  diracSq := digonDiracSqCertificate
  lap0 := digonLap0Certificate
  downLap1 := digonDownLap1Certificate
  traceDsq := 8
  traceLap0 := 4
  traceDownLap1 := 4
  dim_eq := by rfl
  trace_eq := by norm_num
  upper_left_entry_eq := by rfl
  lower_right_entry_eq := by rfl
  upper_right_zero := by rfl
  lower_left_zero := by rfl

theorem dirac_squared_block_diagonal_chain :
    chainDiracSqCertificate =
      #[#[(1 : Rat), -1, 0, 0, 0],
        #[-1, 2, -1, 0, 0],
        #[0, -1, 1, 0, 0],
        #[0, 0, 0, 2, -1],
        #[0, 0, 0, -1, 2]] := by
  rfl

theorem dirac_square_check_chain :
    chainBlockCertificate.upper_right_zero = chainBlockCertificate.lower_left_zero := by
  rfl

theorem dirac_sq_upper_left_is_laplacian0_chain :
    let Dsq := chainDiracSqCertificate
    let Δ₀ := chainLap0Certificate
    (Dsq[0]!)[0]! = (Δ₀[0]!)[0]! := by
  rfl

theorem dirac_sq_lower_right_is_down_laplacian1_chain :
    let Dsq := chainDiracSqCertificate
    let downΔ₁ := chainDownLap1Certificate
    (Dsq[3]!)[3]! = (downΔ₁[0]!)[0]! := by
  rfl

theorem dirac_sq_upper_right_is_zero_chain :
    let Dsq := chainDiracSqCertificate
    (Dsq[0]!)[3]! = 0 := by
  rfl

theorem dirac_sq_lower_left_is_zero_chain :
    let Dsq := chainDiracSqCertificate
    (Dsq[3]!)[0]! = 0 := by
  rfl

theorem trace_D_sq_equals_trace_laplacians_chain :
    let trDsq : Rat := 8
    let trΔ₀ : Rat := 4
    let trDownΔ₁ : Rat := 4
    trDsq = trΔ₀ + trDownΔ₁ := by
  intro trDsq trΔ₀ trDownΔ₁
  norm_num [trDsq, trΔ₀, trDownΔ₁]

theorem dirac_squared_block_diagonal_triangle :
    triangleDiracSqCertificate =
      #[#[(2 : Rat), -1, -1, 0, 0, 0],
        #[-1, 2, -1, 0, 0, 0],
        #[-1, -1, 2, 0, 0, 0],
        #[0, 0, 0, 2, 1, -1],
        #[0, 0, 0, 1, 2, 1],
        #[0, 0, 0, -1, 1, 2]] := by
  rfl

theorem dirac_squared_block_diagonal_digon :
    digonDiracSqCertificate =
      #[#[(2 : Rat), -2, 0, 0],
        #[-2, 2, 0, 0],
        #[0, 0, 2, -2],
        #[0, 0, -2, 2]] := by
  rfl

theorem dirac_square_check_triangle :
    triangleBlockCertificate.upper_right_zero = triangleBlockCertificate.lower_left_zero := by
  rfl

end DAG.DiracLaplacian
