
import Std
import DAG.Basic
import DAG.Util
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

namespace DAG

universe u




structure TwoComplex (α) [BEq α] [Hashable α] where
  base  : HydratedGraph α
  edges : Array (Nat × Nat)
  faces : Array (Nat × Nat × Nat) -- (e_uv, e_vw, e_uw)
  digons : Array (Nat × Nat) -- (e_uv, e_vu) for bidirectional isomorphisms
  deriving Repr

def buildTwoComplex {α} [BEq α] [Hashable α] (h : HydratedGraph α) : TwoComplex α := Id.run do
  let g := h.toGraph
  let n := g.nodes.size

  -- 1. Collect Edges
  let mut edges : Array (Nat × Nat) := #[]
  for u in [:n] do
    for (v, _) in g.forward[u]! do
      edges := edges.push (u, v)

  -- 2. Index Edges for O(1) Lookup
  let mut edgeIndex : Std.HashMap (Nat × Nat) Nat := {}
  for i in [:edges.size] do
    edgeIndex := edgeIndex.insert edges[i]! i

  -- 3. Detect bidirectional edges (digons)
  let mut digons : Array (Nat × Nat) := #[]
  for i in [:edges.size] do
    let (u, v) := edges[i]!
    if let some j := edgeIndex.get? (v, u) then
      -- add each pair only once (i < j) to avoid duplicates
      if i < j then
        digons := digons.push (i, j)

  -- 4. Build Faces (Commutative Triangles)
  -- Optimization: Iterate u -> v, then v -> w, check u -> w
  let mut faces : Array (Nat × Nat × Nat) := #[]
  for i in [:edges.size] do
    let (u, v) := edges[i]!
    for (w, _) in g.forward[v]! do
      if let some k := edgeIndex.get? (u, w) then
        if let some j := edgeIndex.get? (v, w) then
          faces := faces.push (i, j, k)

  return { base := h, edges := edges, faces := faces, digons := digons }

def boundary1 {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Array (Array Rat) :=
  Array.ofFn (fun i : Fin tc.edges.size =>
    Array.ofFn (fun j : Fin tc.base.toGraph.nodes.size =>
      let (u, v) := tc.edges[i.val]
      if j.val = u then (-1 : Rat) else if j.val = v then 1 else 0
    )
  )


def boundary2 {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Array (Array Rat) :=
  Array.ofFn (fun i : Fin (tc.faces.size + tc.digons.size) =>
    Array.ofFn (fun j : Fin tc.edges.size =>
      if h : i.val < tc.faces.size then
        let (e1, e2, e3) := tc.faces[i.val]
        if j.val = e1 then 1 else if j.val = e2 then 1 else if j.val = e3 then (-1) else 0
      else
        let (eU, eV) := tc.digons[i.val - tc.faces.size]
        if j.val = eU then 1 else if j.val = eV then 1 else 0
    )
  )


def matMul (a : Array (Array Rat)) (b : Array (Array Rat)) : Array (Array Rat) := Id.run do
  if a.size = 0 || b.size = 0 then return #[]
  let rows := a.size
  let cols := b[0]!.size
  let inner := b.size
  if a[0]!.size != inner then return #[] -- Dimension mismatch guard
  let mut result := Array.replicate rows (Array.replicate cols 0)
  for i in [:rows] do
    for j in [:cols] do
      let mut sum : Rat := 0
      for k in [:inner] do
        sum := sum + (a[i]!)[k]! * (b[k]!)[j]!
      let row := result[i]!
      result := result.set! i (row.set! j sum)
  return result

def boundarySquaredZero {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Bool :=
  let b1 := boundary1 tc
  let b2 := boundary2 tc
  let prod := matMul b2 b1 -- Note the swapped order!
  prod.all (fun row => row.all (fun x => x == 0))

def eulerCharacteristic {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Int :=
  let v := tc.base.toGraph.nodes.size
  let e := tc.edges.size
  let f := tc.faces.size + tc.digons.size
  v - e + f

def redundancySupport {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Array Nat :=
  tc.faces.map (fun (_, _, e3) => e3)


def gaussianRank (m : Array (Array Rat)) : Nat := Id.run do
  if m.size == 0 then return 0
  let rows := m.size
  let cols := m[0]!.size
  let mut mat := m
  let mut pivotRow := 0
  for j in [:cols] do
    if pivotRow < rows then
      let mut found := false
      for i in [pivotRow:rows] do
        if !found && (mat[i]!)[j]! != 0 then
          let temp := mat[pivotRow]!
          mat := mat.set! pivotRow mat[i]!
          mat := mat.set! i temp
          found := true
      if found then
        let pivotVal := (mat[pivotRow]!)[j]!
        let row := mat[pivotRow]!.map (fun x => x / pivotVal)
        mat := mat.set! pivotRow row
        for i in [:rows] do
          if i != pivotRow then
            let factor := (mat[i]!)[j]!
            let newRow := (mat[i]!.zip mat[pivotRow]!).map (fun (x, y) => x - factor * y)
            mat := mat.set! i newRow
        pivotRow := pivotRow + 1
  return pivotRow

def betti1 {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Int :=
  let b1 := boundary1 tc
  let b2 := boundary2 tc
  let r1 := gaussianRank b1
  let r2 := gaussianRank b2
  (Int.ofNat tc.edges.size) - (Int.ofNat r1) - (Int.ofNat r2)

open Matrix

/-- Boundary operator d1 as Matrix (edges x vertices). -/
def boundary1Matrix {α} [BEq α] [Hashable α] (tc : TwoComplex α) :
    Matrix (Fin tc.edges.size) (Fin tc.base.toGraph.nodes.size) ℚ :=
  λ i j =>
    let (u, v) := tc.edges[i.val]

    if j.val = u then (-1 : ℚ) else if j.val = v then 1 else 0

/-- Boundary operator d2 as Matrix (faces x edges). -/
def boundary2Matrix {α} [BEq α] [Hashable α] (tc : TwoComplex α) :
    Matrix (Fin (tc.faces.size + tc.digons.size)) (Fin tc.edges.size) ℚ :=
  λ i j =>
    if h : i.val < tc.faces.size then
      let (e1, e2, e3) := tc.faces[i.val]
      if j.val = e1 then 1 else if j.val = e2 then 1 else if j.val = e3 then (-1) else 0
    else
      let (eU, eV) := tc.digons[i.val - tc.faces.size]
      if j.val = eU then 1 else if j.val = eV then 1 else 0

theorem boundary1_get_eq_matrix
    {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α)
    (i : Fin tc.edges.size) (j : Fin tc.base.toGraph.nodes.size) :
    ((boundary1 tc)[i.val]!)[j.val]! = boundary1Matrix tc i j := by
  simp [boundary1, boundary1Matrix]

theorem boundary2_get_eq_matrix
    {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α)
    (i : Fin (tc.faces.size + tc.digons.size)) (j : Fin tc.edges.size) :
    ((boundary2 tc)[i.val]!)[j.val]! = boundary2Matrix tc i j := by
  simp [boundary2, boundary2Matrix]

/-- Hodge Laplacian = d1*d1^T + d2^T*d2 as Matrix. -/
def laplacian1Matrix {α} [BEq α] [Hashable α] (tc : TwoComplex α) :
    Matrix (Fin tc.edges.size) (Fin tc.edges.size) ℚ :=
  let d1 := boundary1Matrix tc
  let d2 := boundary2Matrix tc
  d1 * d1ᵀ + d2ᵀ * d2

/-! ## Propositional boundary law -/

/-- The coefficient of the boundary-of-boundary matrix at a face and vertex. -/
def boundarySquaredCoefficient {α} [BEq α] [Hashable α]
    (tc : TwoComplex α)
    (f : Fin (tc.faces.size + tc.digons.size))
    (v : Fin tc.base.toGraph.nodes.size) : ℚ :=
  ∑ e : Fin tc.edges.size,
    boundary2Matrix tc f e * boundary1Matrix tc e v

/-- The native proposition that the stored incidence matrices form a chain complex. -/
def BoundaryLaw {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Prop :=
  ∀ f v, boundarySquaredCoefficient tc f v = 0

/-! A finite boundary complex is a two-complex together with its actual
    coefficient-level boundary law.  The executable Boolean checker remains
    only a readout. -/
def FiniteBoundaryComplex (α) [BEq α] [Hashable α] :=
  { tc : TwoComplex α // BoundaryLaw tc }

theorem boundarySquaredCoefficient_eq_mul_apply
    {α : Type u} [BEq α] [Hashable α] (tc : TwoComplex α)
    (f : Fin (tc.faces.size + tc.digons.size))
    (v : Fin tc.base.toGraph.nodes.size) :
    boundarySquaredCoefficient tc f v =
      (boundary2Matrix tc * boundary1Matrix tc) f v := by
  simp [boundarySquaredCoefficient, Matrix.mul_apply]

theorem boundaryLaw_iff_matrix_zero
    {α : Type u} [BEq α] [Hashable α] (tc : TwoComplex α) :
    BoundaryLaw tc ↔ boundary2Matrix tc * boundary1Matrix tc = 0 := by
  constructor
  · intro h
    ext f v
    rw [← boundarySquaredCoefficient_eq_mul_apply]
    exact h f v
  · intro h f v
    rw [boundarySquaredCoefficient_eq_mul_apply, h]
    rfl

theorem FiniteBoundaryComplex.boundary_matrix_zero
    {α} [BEq α] [Hashable α] (K : FiniteBoundaryComplex α) :
    boundary2Matrix K.1 * boundary1Matrix K.1 = 0 := by
  ext f v
  change (boundary2Matrix K.1 * boundary1Matrix K.1) f v = 0
  calc
    (boundary2Matrix K.1 * boundary1Matrix K.1) f v =
        boundarySquaredCoefficient K.1 f v :=
      (boundarySquaredCoefficient_eq_mul_apply K.1 f v).symm
    _ = 0 := K.2 f v

end DAG
