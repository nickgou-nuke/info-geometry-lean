import DAG.TwoComplex

/-!
# Graph Hodge Theory on the Declaration DAG

Given a `TwoComplex` (vertices, oriented edges, triangular faces), this module
constructs:

- **coboundary operators** `δ₀ = ∂₁ᵀ` and `δ₁ = ∂₂ᵀ`
- **combinatorial Laplacians** `Δ₀ = ∂₁ᵀ ∂₁` (on 0-chains) and
  `Δ₁ = ∂₁ ∂₁ᵀ + ∂₂ᵀ ∂₂` (Hodge Laplacian on 1-chains)
- **graph Dirac operator** `D` such that `D² = Δ` on 0⊕1-chains
- **chiral grading** `Γ` from a node-level `ℤ/2` labelling (e.g. `RepDepth`
  parity or source/sink parity), with verification that `ΓD + DΓ = 0`
  when the labelling is consistent with edge orientation

The Hodge decomposition `C^k = exact ⊕ coexact ⊕ harmonic` means every
k-chain on the declaration graph splits into "derived from lower" +
"generating for higher" + "intrinsic invariant".  On the DAG this
recovers the owner / translator / coherence classification as a theorem
about the graph rather than a naming convention.

All matrices are `Array (Array Rat)` — the same representation used by
`boundary1`/`boundary2` in `TwoComplex.lean`.
-/

namespace DAG

-- ============================================================
-- Matrix utilities
-- ============================================================

/-- Transpose a rational matrix. -/
def matTranspose (m : Array (Array Rat)) : Array (Array Rat) := Id.run do
  if m.size == 0 then return #[]
  let rows := m.size
  let cols := m[0]!.size
  let mut result := Array.replicate cols (Array.replicate rows (0 : Rat))
  for i in [:rows] do
    for j in [:cols] do
      let row := result[j]!
      result := result.set! j (row.set! i m[i]![j]!)
  return result

/-- Entrywise addition of two matrices of the same dimensions. -/
def matAdd (a b : Array (Array Rat)) : Array (Array Rat) := Id.run do
  let mut result := Array.replicate a.size (Array.replicate (a[0]!.size) (0 : Rat))
  for i in [:a.size] do
    let mut row := result[i]!
    for j in [:row.size] do
      row := row.set! j (a[i]![j]! + b[i]![j]!)
    result := result.set! i row
  return result

/-- Diagonal of a square matrix. -/
def matDiag (m : Array (Array Rat)) : Array Rat :=
  Array.ofFn (n := m.size) (fun i => m[i.val]![i.val]!)

/-- Trace of a square matrix. -/
def matTrace (m : Array (Array Rat)) : Rat :=
  (matDiag m).foldl (· + ·) 0

/-- Identity matrix of size n. -/
def matIdentity (n : Nat) : Array (Array Rat) := Id.run do
  let mut m := Array.replicate n (Array.replicate n (0 : Rat))
  for i in [:n] do
    let row := m[i]!
    m := m.set! i (row.set! i (1 : Rat))
  return m

/-- Two matrices are equal if they have the same dimensions and all entries match. -/
def matEqual (a b : Array (Array Rat)) : Bool :=
  if a.size != b.size then false else
  Id.run do
    for i in [:a.size] do
      if a[i]!.size != b[i]!.size then return false
      for j in [:a[i]!.size] do
        if a[i]![j]! != b[i]![j]! then return false
    return true
-- ============================================================

/-- Coboundary δ₀ : C⁰ → C¹, the transpose of ∂₁. -/
def coboundary0 {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Array (Array Rat) :=
  matTranspose (boundary1 tc)

/-- Coboundary δ₁ : C¹ → C², the transpose of ∂₂. -/
def coboundary1 {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Array (Array Rat) :=
  matTranspose (boundary2 tc)

-- ============================================================
-- Combinatorial Laplacians
-- ============================================================

/-- Laplacian Δ₀ = δ₀ᵀ δ₀ = ∂₁ᵀ ∂₁ on 0-chains (n0 × n0).
    This is the standard graph Laplacian. -/
def laplacian0 {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Array (Array Rat) :=
  let b1 := boundary1 tc      -- n1 × n0
  let b1t := matTranspose b1   -- n0 × n1
  matMul b1t b1                -- n0 × n0

/-- Hodge Laplacian Δ₁ = ∂₁ ∂₁ᵀ + ∂₂ᵀ ∂₂ on 1-chains (n1 × n1).
    Kernel = harmonic 1-forms = intrinsic cycles not killed by faces. -/
def laplacian1 {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Array (Array Rat) :=
  let b1 := boundary1 tc       -- n1 × n0
  let b1t := matTranspose b1   -- n0 × n1
  let b2 := boundary2 tc       -- n2 × n1
  let b2t := matTranspose b2   -- n1 × n2
  let down := matMul b1 b1t    -- n1 × n1  (down-Laplacian)
  let up   := matMul b2t b2    -- n1 × n1  (up-Laplacian)
  matAdd down up

-- ============================================================
-- Nullity / Betti via Laplacians
-- ============================================================

/-- Betti number b₀ = dim ker Δ₀ = number of connected components. -/
def betti0 {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Nat :=
  let n0 := tc.base.toGraph.nodes.size
  n0 - gaussianRank (laplacian0 tc)

-- Note: betti1 is already in TwoComplex.lean via rank-nullity on ∂₁, ∂₂.
-- The Laplacian version should agree: b₁ = n1 - rank(Δ₁).
-- We provide the Laplacian-based version for cross-checking.

/-- Betti number b₁ via Hodge Laplacian (should agree with `betti1`). -/
def betti1Hodge {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Nat :=
  let n1 := tc.edges.size
  n1 - gaussianRank (laplacian1 tc)

-- ============================================================
-- Chiral grading
-- ============================================================

/-- A chiral grading assigns ±1 to each vertex (0-cell).
    For example: RepDepth parity, or source/sink parity. -/
structure ChiralGrading (n : Nat) where
  /-- `signs[i] = 1` or `signs[i] = -1` for each vertex i. -/
  signs : Array Rat
  size_eq : signs.size = n

/-- Build a chiral grading from a function `f : Nat → Bool`.
    `true` ↦ +1, `false` ↦ -1. -/
def ChiralGrading.ofBool (n : Nat) (f : Nat → Bool) : ChiralGrading n :=
  { signs := Array.ofFn (n := n) (fun i => if f i.val then (1 : Rat) else (-1 : Rat))
    size_eq := by simp [Array.size_ofFn] }

/-- The chiral grading from RepDepth parity: even depths (+1), odd depths (−1). -/
def chiralGradingFromDepths (n : Nat) (depths : Array Nat) : ChiralGrading n :=
  ChiralGrading.ofBool n (fun i =>
    if h : i < depths.size then depths[i] % 2 == 0 else true)

/-- Diagonal matrix from a chiral grading (n0 × n0). -/
def chiralDiagMatrix (γ : ChiralGrading n) : Array (Array Rat) := Id.run do
  let mut m := Array.replicate n (Array.replicate n (0 : Rat))
  for i in [:n] do
    let row := m[i]!
    m := m.set! i (row.set! i γ.signs[i]!)
  return m

-- ============================================================
-- Graph Dirac operator
-- ============================================================

/-- The graph Dirac operator on 0⊕1 chains.
    ```
    D = ⎡  0    δ₀ ⎤ = ⎡  0    ∂₁ᵀ ⎤
        ⎣  ∂₁   0  ⎦   ⎣  ∂₁   0   ⎦
    ```
    This is an (n0+n1) × (n0+n1) matrix satisfying D² = Δ₀ ⊕ down-Δ₁
    (the "down" part of the Hodge Laplacian on 1-chains, i.e. ∂₁ ∂₁ᵀ). -/
def graphDirac {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Array (Array Rat) := Id.run do
  let b1 := boundary1 tc       -- n1 × n0
  let b1t := matTranspose b1   -- n0 × n1
  let n0 := tc.base.toGraph.nodes.size
  let n1 := tc.edges.size
  let dim := n0 + n1
  let mut mat := Array.replicate dim (Array.replicate dim (0 : Rat))
  -- Upper-right block: δ₀ = ∂₁ᵀ  (rows 0..n0-1, cols n0..n0+n1-1)
  for i in [:n0] do
    for j in [:n1] do
      let row := mat[i]!
      mat := mat.set! i (row.set! (n0 + j) b1t[i]![j]!)
  -- Lower-left block: ∂₁  (rows n0..n0+n1-1, cols 0..n0-1)
  for i in [:n1] do
    for j in [:n0] do
      let row := mat[n0 + i]!
      mat := mat.set! (n0 + i) (row.set! j b1[i]![j]!)
  return mat

-- ============================================================
-- Chiral Dirac and anticommutation check
-- ============================================================

/-- Extend a 0-chain chiral grading Γ₀ to a grading on 0⊕1 chains:
    ```
    Γ = ⎡ Γ₀   0  ⎤
        ⎣  0  −Γ₁ ⎦
    ```
    where Γ₁(e) = Γ₀(target(e)) for each edge e.
    The sign flip on 1-chains is standard: if Γ grades vertices,
    edges inherit the opposite grading to make ΓD + DΓ = 0. -/
def extendedChiralGrading {α} [BEq α] [Hashable α]
    (tc : TwoComplex α) (γ : ChiralGrading tc.base.toGraph.nodes.size)
    : Array (Array Rat) := Id.run do
  let n0 := tc.base.toGraph.nodes.size
  let n1 := tc.edges.size
  let dim := n0 + n1
  let mut mat := Array.replicate dim (Array.replicate dim (0 : Rat))
  -- Vertex block: +Γ₀
  for i in [:n0] do
    let row := mat[i]!
    mat := mat.set! i (row.set! i γ.signs[i]!)
  -- Edge block: −Γ₁ where Γ₁(e) = Γ₀(target(e))
  for i in [:n1] do
    let (_, v) := tc.edges[i]!
    let row := mat[n0 + i]!
    mat := mat.set! (n0 + i) (row.set! (n0 + i) (-γ.signs[v]!))
  return mat

/-- Check whether ΓD + DΓ = 0 (chiral anticommutation).
    Returns `true` when the grading is compatible with the graph Dirac. -/
def chiralAnticommutes {α} [BEq α] [Hashable α]
    (tc : TwoComplex α) (γ : ChiralGrading tc.base.toGraph.nodes.size)
    : Bool :=
  let d := graphDirac tc
  let g := extendedChiralGrading tc γ
  let gd := matMul g d
  let dg := matMul d g
  let sum := matAdd gd dg
  sum.all (fun row => row.all (fun x => x == 0))

-- ============================================================
-- Summary export (for use in #eval or IO)
-- ============================================================

/-- Compact summary of the Hodge invariants of a TwoComplex. -/
structure HodgeSummary where
  nodes    : Nat
  edges    : Nat
  faces    : Nat
  euler    : Int
  b0       : Nat
  b1       : Nat
  b1Hodge  : Nat  -- cross-check via Laplacian
  traceΔ0  : Rat  -- sum of vertex degrees (= 2 × edges)
  diracDim : Nat  -- dimension of the Dirac matrix
  deriving Repr

def hodgeSummary {α} [BEq α] [Hashable α] (tc : TwoComplex α) : HodgeSummary :=
  let n0 := tc.base.toGraph.nodes.size
  let n1 := tc.edges.size
  let n2 := tc.faces.size + tc.digons.size
  { nodes    := n0
    edges    := n1
    faces    := n2
    euler    := eulerCharacteristic tc
    b0       := betti0 tc
    b1       := betti1 tc |>.toNat
    b1Hodge  := betti1Hodge tc
    traceΔ0  := matTrace (laplacian0 tc)
    diracDim := n0 + n1 }

-- ============================================================
-- Spectral invariant computational checks
-- ============================================================

/-- Check Δ₀ is self-adjoint: Δ₀ᵀ = Δ₀. Follows from (AᵀA)ᵀ = AᵀA. -/
def laplacian0SelfAdjointCheck {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Bool :=
  let L := laplacian0 tc
  matEqual (matTranspose L) L

/-- Check Δ₁ is self-adjoint: Δ₁ᵀ = Δ₁. -/
def laplacian1SelfAdjointCheck {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Bool :=
  let L := laplacian1 tc
  matEqual (matTranspose L) L

/-- Check D² = Δ₀ ⊕ (down-Δ₁) — the graph Lichnerowicz formula. -/
def diracSquareCheck {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Bool := Id.run do
  let d := graphDirac tc
  let d2 := matMul d d
  let n0 := tc.base.toGraph.nodes.size
  let n1 := tc.edges.size
  let b1 := boundary1 tc
  let b1t := matTranspose b1
  let expected00 := matMul b1t b1
  let expected11 := matMul b1 b1t
  let mut ok := true
  for i in [:n0] do
    for j in [:n0] do
      if d2[i]![j]! != expected00[i]![j]! then ok := false
  for i in [:n1] do
    for j in [:n1] do
      if d2[n0 + i]![n0 + j]! != expected11[i]![j]! then ok := false
  for i in [:n0] do
    for j in [:n1] do
      if d2[i]![n0 + j]! != 0 || d2[n0 + j]![i]! != 0 then ok := false
  return ok

end DAG
