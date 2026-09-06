import DAG.TwoComplex
import DAG.GraphHodge
import DAG.HodgeTheorems
import DAG.CocycleBridge

/-!
# DAG.ConnesHodgeBridge

Bridge data from discrete Hodge readouts to a Connes-style correspondence
surface. Finite Hodge data is owned by `DAG.GraphHodge`/`DAG.HodgeTheorems`.
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
  { complex := tc
    edgeCount := tc.edges.size
    harmonicDim := betti1Hodge tc
    cocycleDimUpperBound := betti1Hodge tc
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

end DAG.ConnesHodgeBridge
