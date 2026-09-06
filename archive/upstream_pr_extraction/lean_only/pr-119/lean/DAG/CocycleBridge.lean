import DAG.GraphHodge
import DAG.HodgeTheorems
import DAG.TwoComplex

/-!
# DAG.CocycleBridge

Bridge data for packaging the computable Hodge invariants of a `TwoComplex`.
The executable owners are `DAG.TwoComplex`, `DAG.GraphHodge`, and the concrete
checks in `DAG.HodgeTheorems`. This file is a readout/packaging layer, not a
continuous Connes-cocycle theorem owner.
-/

open DAG

namespace DAG.CocycleBridge

/--
The Hodge-cocycle data structure. Given a `TwoComplex`, it packages the
computable Hodge decomposition invariants used by downstream retrieval and
bridge layers.
-/
structure HodgeCocycleData (α : Type) [BEq α] [Hashable α] where
  complex : TwoComplex α
  /-- First Betti number = dim ker Δ₁ = dim H¹ -/
  betti1 : Nat
  /-- Euler characteristic = Σ(-1)ᵏβₖ -/
  eulerChar : Int
  /-- Hodge decomposition: (rank ∂₁ᵀ, rank ∂₂, b₁) -/
  hodgeDecomp : Nat × Nat × Nat
  deriving Repr

/-- Construct HodgeCocycleData from any TwoComplex. -/
def fromTwoComplex {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) :
    HodgeCocycleData α :=
  { complex := tc
    betti1 := (betti1 tc).toNat
    eulerChar := eulerCharacteristic tc
    hodgeDecomp :=
      ( gaussianRank (matTranspose (boundary1 tc))
      , gaussianRank (boundary2 tc)
      , betti1Hodge tc )
  }

/-
Analytic or categorical identifications with continuous cocycles must be proved
by an owner theorem outside this finite readout layer.
-/

end DAG.CocycleBridge
