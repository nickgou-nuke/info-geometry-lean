import DAG.TwoComplex
import DAG.GraphHodge
import DAG.CocycleBridge

/-!
# DAG.ConnesHodgeBridge

Bridge data from discrete Hodge readouts to a Connes-style correspondence
surface. Finite Hodge data is owned by `DAG.GraphHodge`.
Continuous modular-flow and analytic Connes-cocycle claims remain outside this
finite correspondence package.
-/

open DAG

namespace DAG.ConnesHodgeBridge

/--
Finite Connes-style correspondence readout.

The Hodge Betti number is recorded as an upper-bound field for later cocycle
constructions; no analytic cocycle equivalence is asserted by this structure.
-/
structure ConnesCorrespondence (α : Type) [BEq α] [Hashable α] where
  complex : TwoComplex α
  /-- Number of edges = dimension of 1-chains -/
  edgeCount : Nat
  /-- Dimension of harmonic 1-chains = b₁ -/
  harmonicDim : Nat
  /-- Maximum number of independent Connes 1-cocycles = b₁ -/
  cocycleDimUpperBound : Nat
  /-- Euler characteristic = index of Dirac operator -/
  eulerChar : Int
  deriving Repr

/-- Construct Connes correspondence data from any TwoComplex. -/
def fromTwoComplex {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) :
    ConnesCorrespondence α :=
  let b1 := betti1Hodge tc
  { complex := tc
    edgeCount := tc.edges.size
    harmonicDim := b1
    cocycleDimUpperBound := b1
    eulerChar := eulerCharacteristic tc
  }

/--
Map a DAG-side Hodge data package to the correspondence readout package.
-/
def fromHodgeData {α : Type} [BEq α] [Hashable α]
    (hd : DAG.CocycleBridge.HodgeCocycleData α) : ConnesCorrespondence α :=
  { complex := hd.complex
    edgeCount := hd.complex.edges.size
    harmonicDim := hd.betti1
    cocycleDimUpperBound := hd.betti1
    eulerChar := hd.eulerChar
  }

/-! ## Definitional Projections and Invariants -/

@[simp]
theorem fromTwoComplex_edgeCount {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) :
    (fromTwoComplex tc).edgeCount = tc.edges.size :=
  rfl

@[simp]
theorem fromTwoComplex_harmonicDim {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) :
    (fromTwoComplex tc).harmonicDim = betti1Hodge tc :=
  rfl

@[simp]
theorem fromTwoComplex_cocycleDimUpperBound {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) :
    (fromTwoComplex tc).cocycleDimUpperBound = betti1Hodge tc :=
  rfl

@[simp]
theorem fromTwoComplex_eulerChar {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) :
    (fromTwoComplex tc).eulerChar = eulerCharacteristic tc :=
  rfl

@[simp]
theorem fromHodgeData_edgeCount {α : Type} [BEq α] [Hashable α] (hd : DAG.CocycleBridge.HodgeCocycleData α) :
    (fromHodgeData hd).edgeCount = hd.complex.edges.size :=
  rfl

@[simp]
theorem fromHodgeData_harmonicDim {α : Type} [BEq α] [Hashable α] (hd : DAG.CocycleBridge.HodgeCocycleData α) :
    (fromHodgeData hd).harmonicDim = hd.betti1 :=
  rfl

@[simp]
theorem fromHodgeData_cocycleDimUpperBound {α : Type} [BEq α] [Hashable α] (hd : DAG.CocycleBridge.HodgeCocycleData α) :
    (fromHodgeData hd).cocycleDimUpperBound = hd.betti1 :=
  rfl

@[simp]
theorem fromHodgeData_eulerChar {α : Type} [BEq α] [Hashable α] (hd : DAG.CocycleBridge.HodgeCocycleData α) :
    (fromHodgeData hd).eulerChar = hd.eulerChar :=
  rfl

/-- Invariant: Harmonic dimension equals cocycle dimension upper bound for `fromTwoComplex`. -/
theorem fromTwoComplex_harmonicDim_eq_cocycleDimUpperBound {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) :
    (fromTwoComplex tc).harmonicDim = (fromTwoComplex tc).cocycleDimUpperBound :=
  rfl

/-- Invariant: Harmonic dimension equals cocycle dimension upper bound for `fromHodgeData`. -/
theorem fromHodgeData_harmonicDim_eq_cocycleDimUpperBound {α : Type} [BEq α] [Hashable α] (hd : DAG.CocycleBridge.HodgeCocycleData α) :
    (fromHodgeData hd).harmonicDim = (fromHodgeData hd).cocycleDimUpperBound :=
  rfl

/-- Alias matching alternate naming convention. -/
theorem harmonicDim_eq_cocycleDimUpperBound_fromTwoComplex {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) :
    (fromTwoComplex tc).harmonicDim = (fromTwoComplex tc).cocycleDimUpperBound :=
  rfl

/-- Alias matching alternate naming convention. -/
theorem harmonicDim_eq_cocycleDimUpperBound_fromHodgeData {α : Type} [BEq α] [Hashable α] (hd : DAG.CocycleBridge.HodgeCocycleData α) :
    (fromHodgeData hd).harmonicDim = (fromHodgeData hd).cocycleDimUpperBound :=
  rfl

/-- Coherence: edge counts agree when bridging through HodgeCocycleData. -/
theorem fromHodgeData_fromTwoComplex_edgeCount {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) :
    (fromHodgeData (DAG.CocycleBridge.fromTwoComplex tc)).edgeCount = (fromTwoComplex tc).edgeCount :=
  rfl

/-- Coherence: Euler characteristics agree when bridging through HodgeCocycleData. -/
theorem fromHodgeData_fromTwoComplex_eulerChar {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) :
    (fromHodgeData (DAG.CocycleBridge.fromTwoComplex tc)).eulerChar = (fromTwoComplex tc).eulerChar :=
  rfl

end DAG.ConnesHodgeBridge
