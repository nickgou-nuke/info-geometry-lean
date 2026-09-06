import DAG.GraphHodge

namespace DAG.BlockDecomposition

open DAG

/-- Three-layer block data on `C⁰ ⊕ C¹ ⊕ C²` for a finite `TwoComplex`. -/
structure BlockDecomp (α : Type) [BEq α] [Hashable α] where
  complex : TwoComplex α
  dim : Nat × Nat × Nat
  dirac : Array (Array Rat)
  chiral : Array (Array Rat)
  laplacian : Array (Array Rat)
  laplacian0 : Array (Array Rat)
  laplacian1 : Array (Array Rat)
  laplacian2 : Array (Array Rat)
  deriving Repr

/--
Build the explicit `C⁰ ⊕ C¹ ⊕ C²` block decomposition from the boundary maps of
a `TwoComplex`.
-/
def ofTwoComplex {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) : BlockDecomp α :=
  let n0 := tc.base.toGraph.nodes.size
  let n1 := tc.edges.size
  let n2 := tc.faces.size + tc.digons.size
  let dim := n0 + n1 + n2
  let b1 := boundary1 tc
  let b1t := matTranspose b1
  let b2 := boundary2 tc
  let b2t := matTranspose b2
  let Δ₀ := matMul b1t b1
  let downΔ₁ := matMul b1 b1t
  let upΔ₁ :=
    if b2.size == 0 then
      Array.replicate tc.edges.size (Array.replicate tc.edges.size (0 : Rat))
    else
      matMul b2t b2
  let Δ₁ := matAdd downΔ₁ upΔ₁
  let Δ₂ := matMul b2 b2t
  let D := Id.run do
    let mut mat := Array.replicate dim (Array.replicate dim (0 : Rat))
    for i in [:n0] do
      for j in [:n1] do
        let row := mat[i]!
        mat := mat.set! i (row.set! (n0 + j) b1t[i]![j]!)
    for i in [:n1] do
      for j in [:n0] do
        let row := mat[n0 + i]!
        mat := mat.set! (n0 + i) (row.set! j b1[i]![j]!)
    for i in [:n1] do
      for j in [:n2] do
        let row := mat[n0 + i]!
        mat := mat.set! (n0 + i) (row.set! (n0 + n1 + j) b2t[i]![j]!)
    for i in [:n2] do
      for j in [:n1] do
        let row := mat[n0 + n1 + i]!
        mat := mat.set! (n0 + n1 + i) (row.set! (n0 + j) b2[i]![j]!)
    mat
  let Γ := Id.run do
    let mut mat := Array.replicate dim (Array.replicate dim (0 : Rat))
    for i in [:n0] do
      let row := mat[i]!
      mat := mat.set! i (row.set! i (1 : Rat))
    for i in [:n1] do
      let row := mat[n0 + i]!
      mat := mat.set! (n0 + i) (row.set! (n0 + i) (-1 : Rat))
    for i in [:n2] do
      let row := mat[n0 + n1 + i]!
      mat := mat.set! (n0 + n1 + i) (row.set! (n0 + n1 + i) (1 : Rat))
    mat
  let Δ := Id.run do
    let mut mat := Array.replicate dim (Array.replicate dim (0 : Rat))
    for i in [:n0] do
      for j in [:n0] do
        let row := mat[i]!
        mat := mat.set! i (row.set! j Δ₀[i]![j]!)
    for i in [:n1] do
      for j in [:n1] do
        let row := mat[n0 + i]!
        mat := mat.set! (n0 + i) (row.set! (n0 + j) Δ₁[i]![j]!)
    for i in [:n2] do
      for j in [:n2] do
        let row := mat[n0 + n1 + i]!
        mat := mat.set! (n0 + n1 + i) (row.set! (n0 + n1 + j) Δ₂[i]![j]!)
    mat
  { complex := tc
    dim := (n0, n1, n2)
    dirac := D
    chiral := Γ
    laplacian := Δ
    laplacian0 := Δ₀
    laplacian1 := Δ₁
    laplacian2 := Δ₂ }

/-- The three-layer Dirac operator associated to a `TwoComplex`. -/
def diracOf {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) : Array (Array Rat) :=
  (ofTwoComplex tc).dirac

/-- The three-layer chirality matrix associated to a `TwoComplex`. -/
def chiralOf {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) : Array (Array Rat) :=
  (ofTwoComplex tc).chiral

/-- The three-layer block Laplacian associated to a `TwoComplex`. -/
def laplacianOf {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) : Array (Array Rat) :=
  (ofTwoComplex tc).laplacian

/-- The dimensions `(n₀, n₁, n₂)` of a `TwoComplex`. -/
def dimensionsOf {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) :
    Nat × Nat × Nat :=
  (tc.base.toGraph.nodes.size, tc.edges.size, tc.faces.size + tc.digons.size)

@[simp] theorem dimensionsOf_eq {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) :
    dimensionsOf tc = (tc.base.toGraph.nodes.size, tc.edges.size,
      tc.faces.size + tc.digons.size) :=
  rfl

@[simp] theorem diracOf_eq {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) :
    diracOf tc = (ofTwoComplex tc).dirac :=
  rfl

@[simp] theorem chiralOf_eq {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) :
    chiralOf tc = (ofTwoComplex tc).chiral :=
  rfl

@[simp] theorem laplacianOf_eq {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) :
    laplacianOf tc = (ofTwoComplex tc).laplacian :=
  rfl

end DAG.BlockDecomposition
