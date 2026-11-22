/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Std
import DAG.Basic
import DAG.Util
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

namespace DAG




structure TwoComplex (α) [BEq α] [Hashable α] where
  base  : HydratedGraph α
  edges : Array (Nat × Nat)
  faces : Array (Nat × Nat × Nat) -- (e_uv, e_vw, e_uw)
  digons : Array (Nat × Nat) -- (e_uv, e_vu) for bidirectional isomorphisms
  deriving Repr

/-- The indexed payloads of a `TwoComplex` are in range for their carriers.
This is a separate predicate rather than a structure field so existing
constructors can represent malformed input for validation and diagnostics. -/
def HasValidIndices {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Prop :=
  (∀ i : Fin tc.edges.size,
    (tc.edges[i.val]).1 < tc.base.toGraph.nodes.size ∧
      (tc.edges[i.val]).2 < tc.base.toGraph.nodes.size) ∧
  (∀ i : Fin tc.faces.size,
    let (e1, e2, e3) := tc.faces[i.val]
    e1 < tc.edges.size ∧ e2 < tc.edges.size ∧ e3 < tc.edges.size) ∧
  (∀ i : Fin tc.digons.size,
    let (e1, e2) := tc.digons[i.val]
    e1 < tc.edges.size ∧ e2 < tc.edges.size)

def buildTwoComplex {α} [BEq α] [Hashable α] (h : HydratedGraph α) : TwoComplex α := Id.run do
  let g := h.toGraph
  let n := g.nodes.size

  -- 1. Collect Edges
  let mut edges : Array (Nat × Nat) := #[]
  let mut edgeKinds : Array EdgeKind := #[]
  for u in [:n] do
    for (v, kind) in g.forward[u]! do
      edges := edges.push (u, v)
      edgeKinds := edgeKinds.push kind

  -- 2. Index every edge occurrence. Endpoint pairs need not be unique: the
  -- graph may contain parallel dependencies with different kinds.
  let mut edgeIndices : Std.HashMap (Nat × Nat) (Array Nat) := {}
  let mut outgoingEdgeIndices : Array (Array Nat) := Array.replicate n #[]
  for i in [:edges.size] do
    let endpoints := edges[i]!
    edgeIndices := edgeIndices.insert endpoints ((edgeIndices.getD endpoints #[]).push i)
    let (u, _) := endpoints
    if u < n then
      outgoingEdgeIndices := outgoingEdgeIndices.set! u (outgoingEdgeIndices[u]!.push i)

  -- 3. Detect bidirectional edges (digons)
  let mut digons : Array (Nat × Nat) := #[]
  let mut paired : Array Bool := Array.replicate edges.size false
  for i in [:edges.size] do
    let (u, v) := edges[i]!
    if !paired[i]! then
      let mut reverse? : Option Nat := none
      for j in [i + 1:edges.size] do
        if reverse?.isNone && !paired[j]! && edges[j]! == (v, u) &&
            edgeKinds.getD j EdgeKind.type == edgeKinds.getD i EdgeKind.type then
          reverse? := some j
      if let some j := reverse? then
        digons := digons.push (i, j)
        paired := paired.set! i true
        paired := paired.set! j true

  -- 4. Build faces (commutative triangles), retaining all parallel edge
  -- occurrences. Degenerate triples are not 2-cells.
  let mut faces : Array (Nat × Nat × Nat) := #[]
  for i in [:edges.size] do
    let (u, v) := edges[i]!
    if u != v && v < n then
      for j in outgoingEdgeIndices[v]! do
        let (_, w) := edges[j]!
        if v != w && u != w then
          let shortcutEdges := edgeIndices.getD (u, w) #[]
          for k in shortcutEdges do
            faces := faces.push (i, j, k)

  return { base := h, edges := edges, faces := faces, digons := digons }

/-- Cellular incidence coefficient as the signed sum of endpoint occurrences.
If an edge is a loop, its source and target contributions cancel. -/
def incidenceBoundaryCoeff (u v j : Nat) : Rat :=
  (if j = u then (-1 : Rat) else 0) + (if j = v then 1 else 0)

def boundary1 {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Array (Array Rat) :=
  Array.ofFn (fun i : Fin tc.edges.size =>
    Array.ofFn (fun j : Fin tc.base.toGraph.nodes.size =>
      let (u, v) := tc.edges[i.val]
      incidenceBoundaryCoeff u v j.val
    )
  )

/-- Signed occurrence coefficient for a triangular face boundary. Repeated
edge indices contribute once for every occurrence, with its orientation sign. -/
def faceBoundaryCoeff (e1 e2 e3 j : Nat) : Rat :=
  (if j = e1 then 1 else 0) + (if j = e2 then 1 else 0) -
    (if j = e3 then 1 else 0)

/-- Signed occurrence coefficient for a digon boundary. Both edge occurrences
contribute positively, including when their indices coincide. -/
def digonBoundaryCoeff (eU eV j : Nat) : Rat :=
  (if j = eU then 1 else 0) + (if j = eV then 1 else 0)


def boundary2 {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Array (Array Rat) :=
  Array.ofFn (fun i : Fin (tc.faces.size + tc.digons.size) =>
    Array.ofFn (fun j : Fin tc.edges.size =>
      if h : i.val < tc.faces.size then
        let (e1, e2, e3) := tc.faces[i.val]
        faceBoundaryCoeff e1 e2 e3 j.val
      else
        let (eU, eV) := tc.digons[i.val - tc.faces.size]
        digonBoundaryCoeff eU eV j.val
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
    incidenceBoundaryCoeff u v j.val

/-- Incidence is the sum of the source and target contributions. In particular,
a loop has zero boundary because its two endpoint contributions cancel. -/
theorem boundary1Matrix_self_loop_entry_zero {α} [BEq α] [Hashable α]
    (tc : TwoComplex α) (i : Fin tc.edges.size) (j : Fin tc.base.toGraph.nodes.size)
    (hloop : (tc.edges[i.val]).1 = (tc.edges[i.val]).2) : boundary1Matrix tc i j = 0 := by
  simp only [boundary1Matrix, incidenceBoundaryCoeff]
  rw [hloop]
  split_ifs <;> norm_num

/-- Boundary operator d2 as Matrix (faces x edges). -/
def boundary2Matrix {α} [BEq α] [Hashable α] (tc : TwoComplex α) :
    Matrix (Fin (tc.faces.size + tc.digons.size)) (Fin tc.edges.size) ℚ :=
  λ i j =>
    if h : i.val < tc.faces.size then
      let (e1, e2, e3) := tc.faces[i.val]
      faceBoundaryCoeff e1 e2 e3 j.val
    else
      let (eU, eV) := tc.digons[i.val - tc.faces.size]
      digonBoundaryCoeff eU eV j.val

/-- Hodge Laplacian = d1*d1^T + d2^T*d2 as Matrix. -/
def laplacian1Matrix {α} [BEq α] [Hashable α] (tc : TwoComplex α) :
    Matrix (Fin tc.edges.size) (Fin tc.edges.size) ℚ :=
  let d1 := boundary1Matrix tc
  let d2 := boundary2Matrix tc
  d1 * d1ᵀ + d2ᵀ * d2

end DAG

