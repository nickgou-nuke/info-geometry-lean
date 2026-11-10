/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
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
  /-- Finite upper-bound slot for a future cocycle construction. This readout
  sets it to the ambient 1-cochain dimension; it does not count cocycles. -/
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
    cocycleDimUpperBound := tc.edges.size
    eulerChar := eulerCharacteristic tc
  }

/--
Map a DAG-side Hodge data package to the correspondence readout package.
-/
def fromHodgeData {α : Type} [BEq α] [Hashable α]
    (hd : DAG.CocycleBridge.HodgeCocycleData α) : ConnesCorrespondence α :=
  { complex := hd.complex
    edgeCount := hd.complex.edges.size
    harmonicDim := hd.hodgeDecomp.2.2
    cocycleDimUpperBound := hd.complex.edges.size
    eulerChar := hd.eulerChar
  }

/-! ## Finite cochain dimension bounds -/

/-- For a raw `TwoComplex`, the Hodge-Laplacian nullity is bounded by the number
of edge coordinates: it is the edge count minus a nonnegative computed rank. -/
theorem fromTwoComplex_harmonicDim_le_cocycleDimUpperBound
    {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) :
    (fromTwoComplex tc).harmonicDim ≤ (fromTwoComplex tc).cocycleDimUpperBound := by
  change betti1Hodge tc ≤ tc.edges.size
  unfold betti1Hodge
  exact Nat.sub_le _ _

/-- For the canonical derived Hodge package, its harmonic dimension is bounded
by the ambient 1-cochain dimension recorded by the edge coordinates. -/
theorem fromHodgeData_harmonicDim_le_cocycleDimUpperBound
    {α : Type} [BEq α] [Hashable α] (hd : DAG.CocycleBridge.HodgeCocycleData α) :
    (fromHodgeData hd).harmonicDim ≤ (fromHodgeData hd).cocycleDimUpperBound := by
  change hd.hodgeDecomp.2.2 ≤ hd.complex.edges.size
  exact hd.hodgeHarmonicDim_le_edges

end DAG.ConnesHodgeBridge
