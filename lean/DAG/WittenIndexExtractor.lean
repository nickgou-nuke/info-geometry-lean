import DAG.TwoComplex
import DAG.CocycleBridge

/-!
# Witten Index — χ = β₀ - β₁ from TwoComplex

Computes the Witten index = Euler characteristic of a TwoComplex.

The Witten index is a topological invariant:
  χ = 0 → anomaly-free (equal e⁺ and e⁻ zero modes)
  χ ≠ 0 → topological anomaly (net chiral charge on boundary)

Uses the existing `eulerCharacteristic` and `hodgeSummary` from
TwoComplex.lean and CocycleBridge.lean.

For extracting the dependency graph from a Lean module, see
`WittenIndexExtractor.lean` (metaprogram — structural debt).
-/

namespace DAG.WittenIndex

open DAG

/--
Compute the Witten index for a TwoComplex.

χ = V - E + F = β₀ - β₁

On the DAG: V = declarations, E = dependencies, F = commutative sub-diagrams.
-/
def ofTwoComplex {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) : Int :=
  eulerCharacteristic tc

/--
Full diagnostic: Witten index, Betti numbers, Hodge summary.
-/
def diagnostic {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) : HodgeSummary :=
  hodgeSummary tc

end DAG.WittenIndex
