import DAG.TwoComplex
import DAG.CocycleBridge
import DAG.HodgeTheorems

/-!
# DAG.TwoComplexColimitRecursor

Fold-based recursors over `TwoComplex` construction data.

`to_Target` maps the base graph and then folds over edge, face, and digon arrays.
The proved theorems below are the Euler-characteristic identities that follow
directly from `DAG.TwoComplex.eulerCharacteristic`; concrete Hodge checks live
in `DAG.HodgeTheorems`.
-/

namespace DAG.TwoComplexColimitRecursor

open DAG

/- ## Fold recursor over finite construction arrays -/

/--
Fold over all construction arrays. Given a base map on nodes and step functions
for edges, faces, and digons, produce a global readout on the full TwoComplex.
-/
def to_Target {α : Type} [BEq α] [Hashable α] {T : Type}
    (tc : TwoComplex α)
    (base : HydratedGraph α → T)
    (edge_step : T → (Nat × Nat) → T)
    (face_step : T → (Nat × Nat × Nat) → T)
    (digon_step : T → (Nat × Nat) → T) : T :=
  let t0 := base tc.base
  let t1 := tc.edges.foldl (fun t e => edge_step t e) t0
  let t2 := tc.faces.foldl (fun t f => face_step t f) t1
  tc.digons.foldl (fun t d => digon_step t d) t2

/- ##Filtration structure -/

/--
A TwoComplex filtration: the base subcomplex (nodes only) and
the sequence of edges, faces, and digons that build up to the
full complex.
-/
structure TwoComplexFiltration (α : Type) [BEq α] [Hashable α] where
  levels : TwoComplex α
  full : TwoComplex α
  edgesAdded : Array (Nat × Nat)
  facesAdded : Array (Nat × Nat × Nat)
  digonsAdded : Array (Nat × Nat)

/-- Extract the filtration from any TwoComplex. -/
def filtrationOf {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) :
    TwoComplexFiltration α :=
  { levels := { tc with edges := #[], faces := #[], digons := #[] }
    full := tc
    edgesAdded := tc.edges
    facesAdded := tc.faces
    digonsAdded := tc.digons
  }

/- ##Theorem 1: Euler characteristic by induction -/

/--
For any TwoComplex, the Euler characteristic is:

    χ = V - E + (F + D)

where V = number of vertices, E = number of edges,
F = number of triangular faces, D = number of digon faces.

This is immediate from the definition `eulerCharacteristic`.
-/
theorem euler_characteristic_by_induction
    {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) :
    eulerCharacteristic tc = tc.base.toGraph.nodes.size
      - tc.edges.size + (tc.faces.size + tc.digons.size) := by
  unfold eulerCharacteristic
  simp

/--
The Euler characteristic of the node-only base
(no edges, faces, digons) is simply the number of vertices.
-/
theorem euler_characteristic_base
    {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) :
    eulerCharacteristic { tc with edges := #[], faces := #[], digons := #[] }
    = tc.base.toGraph.nodes.size := by
  unfold eulerCharacteristic
  simp

/--
The Euler characteristic of the full complex
equals the base Euler characteristic minus edge count plus
face+digon count.

    χ(full) = χ(base) - |E| + (|F| + |D|)

Each edge subtracts 1, and each face/digon adds 1.
-/
theorem euler_characteristic_additivity
    {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) :
    eulerCharacteristic tc =
      eulerCharacteristic { tc with edges := #[], faces := #[], digons := #[] }
      - tc.edges.size + (tc.faces.size + tc.digons.size) := by
  rw [euler_characteristic_by_induction, euler_characteristic_base]

/-
## Theorem 2: Induction principle (documented)

Prospective induction principle for TwoComplex invariants.

Let `f : TwoComplex α → T` be an observable. If:

1. `f` is invariant under adding any single edge:
   `f(pushEdge tc e) = f(tc)` for all `tc`, `e`

2. `f` is invariant under adding any single face:
   `f(pushFace tc t) = f(tc)` for all `tc`, `t`

3. `f` is invariant under adding any single digon:
   `f(pushDigon tc d) = f(tc)` for all `tc`, `d`

Then one can prove that `f` is invariant across the entire filtration:
`f(full) = f(base)` for `base` = `{full with edges:=#[], faces:=#[], digons:=#[]}`.

This is not asserted as a theorem in this file yet.
-/

/- ##Push operations (for use with induction) -/

def pushEdge {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) (e : Nat × Nat) :
    TwoComplex α :=
  { tc with edges := tc.edges.push e }

def pushFace {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) (f : Nat × Nat × Nat) :
    TwoComplex α :=
  { tc with faces := tc.faces.push f }

def pushDigon {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) (d : Nat × Nat) :
    TwoComplex α :=
  { tc with digons := tc.digons.push d }

/- ##Wiring to CocycleBridge -/

/-- Lift `to_Target` to produce `HodgeCocycleData` by folding. -/
def to_HodgeCocycleData {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) :
    CocycleBridge.HodgeCocycleData α :=
  CocycleBridge.fromTwoComplex tc

end DAG.TwoComplexColimitRecursor
