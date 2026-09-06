import Std
import DAG.TwoComplex
import DAG.Topo

/-!
# DAG Dominators

Computes dominator sets for a finite DAG by topological dataflow:
for each node, intersect the already-computed dominator sets of its
predecessors and then add the node itself. For a `TwoComplex`, this identifies:

- **Causal bottlenecks**: nodes that dominate large subgraphs → "light cones"
- **Immediate dominators (idom)**: the unique closest dominator of each node
- **Dominator frontier**: where definitions first become visible
- **Causal past/future**: the set of nodes strictly before/after a given node

## Physical meaning

| DAG structure            | Physics interpretation                     |
|---------------------------|--------------------------------------------|
| dominator tree            | causal structure / RG flow direction        |
| immediate dominator       | nearest causal ancestor / parent in lightcone |
| dominator frontier        | event horizon / causal boundary             |
| nodes dominated by n      | future light cone of n                      |
| sink (dominates all)      | heat death / equilibrium state              |

The executable smoke theorems at the bottom cover chain, diamond, and
multi-root cases. Graph evidence from this module remains navigation evidence;
Lean owner files still decide theorem truth.
-/

namespace DAG.Dominators

open DAG

-- ============================================================
-- Bit-vector utilities for efficient dominator sets
-- ============================================================

private def boolVecTrue (byteWidth : Nat) : ByteArray :=
  ByteArray.mk (arrayReplicate byteWidth (0xFF : UInt8))

private def boolVecZero (byteWidth : Nat) : ByteArray :=
  ByteArray.mk (arrayReplicate byteWidth (0 : UInt8))

private def boolVecAnd (a b : ByteArray) : ByteArray :=
  Id.run do
    let mut r := ByteArray.empty
    for i in [:a.size] do
      r := r.push (a[i]! &&& b[i]!)
    r

private def boolVecSet (a : ByteArray) (i : Nat) : ByteArray :=
  let bi := i / 8
  let bit : UInt8 := 1 <<< (i % 8).toUInt8
  a.set! bi (a[bi]! ||| bit)

/--
Compute dominator sets as bit vectors for all nodes of a DAG.

`preds[i]` = predecessors of node i in topological order.
`order` = topological order (list of all nodes).
-/
def dominators (preds : Array (Array Nat)) (order : Array Nat) : Array ByteArray := Id.run do
  let m := preds.size
  let byteWidth := (m + 7) / 8
  let mut dom := arrayReplicate m (boolVecTrue byteWidth)

  for u in order do
    let ps := preds[u]!
    let base :=
      match ps[0]? with
      | none => boolVecZero byteWidth
      | some p0 =>
          Id.run do
            let mut acc := dom[p0]!
            for i in [1:ps.size] do
              acc := boolVecAnd acc (dom[ps[i]!]!)
            acc
    dom := dom.set! u (boolVecSet base u)

  dom

/--
Test whether `a` dominates `b`: every path from source to `b` passes through `a`.
-/
def dominates (dom : Array ByteArray) (a b : Nat) : Bool :=
  let bi := a / 8
  let bit : UInt8 := 1 <<< (a % 8).toUInt8
  ((dom[b]!)[bi]! &&& bit) != 0

/-- Strict dominators of `n`, i.e. dominators excluding `n` itself. -/
def strictDominators (dom : Array ByteArray) (n : Nat) : Array Nat := Id.run do
  let mut out := #[]
  for d in [:dom.size] do
    if d != n && dominates dom d n then
      out := out.push d
  return out

/--
Immediate dominator: the strict dominator closest to `n`.

The closest strict dominator is the maximal element in the dominance order:
every other strict dominator still dominates it. This intentionally ranges over
all strict dominators, not only direct predecessors. In a diamond
`0 → 1 → 3` and `0 → 2 → 3`, the immediate dominator of `3` is `0`, which is
not a direct predecessor.
-/
def immediateDominator (dom : Array ByteArray) (n : Nat) : Option Nat := Id.run do
  let candidates := strictDominators dom n
  for d in candidates do
    if candidates.all (fun e => e == d || dominates dom e d) then
      return some d
  return none

/--
Build the immediate dominator array for all nodes.
Returns `idom[i] = immediateDominator i` (none for source).
-/
def buildIdom (preds : Array (Array Nat)) (dom : Array ByteArray) : Array (Option Nat) := Id.run do
  let mut idom := arrayReplicate preds.size (none : Option Nat)
  for i in [:preds.size] do
    if !preds[i]!.isEmpty then
      idom := idom.set! i (immediateDominator dom i)
  return idom

/--
**Light cone**: the set of nodes strictly dominated by `n` (future light cone)
plus the set of nodes that strictly dominate `n` (past light cone).
-/
def lightcone (dom : Array ByteArray) (n : Nat) : (Array Nat × Array Nat) := Id.run do
  let m := dom.size
  let mut future := #[]
  let mut past := #[]
  for i in [:m] do
    if i != n then
      if dominates dom n i then
        future := future.push i
      if dominates dom i n then
        past := past.push i
  return (future, past)

/--
**Dominator frontier**: nodes where a definition first becomes visible.
DF[n] = { z | ∃ pred ∈ preds[z] : n dominates pred ∧ n does not strictly dominate z }

This is the set of nodes where the dominance relationship breaks —
the "event horizon" of node n's influence.
-/
def dominatorFrontier (preds : Array (Array Nat)) (dom : Array ByteArray) (n : Nat) : Array Nat := Id.run do
  let m := preds.size
  let mut frontier := #[]
  for z in [:m] do
    if !dominates dom n z || n == z then
      -- n does not strictly dominate z (or n == z)
      for p in preds[z]! do
        if dominates dom n p then
          frontier := frontier.push z
          break
  return frontier

/--
Build predecessor lists for all nodes from the TwoComplex edges.
preds[i] = array of all j such that edge j→i exists.
-/
def buildPreds {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Array (Array Nat) := Id.run do
  let n := tc.base.toGraph.nodes.size
  let mut preds := arrayReplicate n #[]
  for (u, v) in tc.edges do
    preds := preds.set! v (preds[v]!.push u)
  return preds

/-- Build successor lists for all nodes from the TwoComplex edges. -/
def buildSuccs {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Array (Array Nat) := Id.run do
  let n := tc.base.toGraph.nodes.size
  let mut succs := arrayReplicate n #[]
  for (u, v) in tc.edges do
    succs := succs.set! u (succs[u]!.push v)
  return succs

/--
Topological order for the TwoComplex edge relation. If the relation is not a
DAG, `topo` returns a partial order; in that case we fall back to node order so
the analysis remains total but should be treated as non-authoritative evidence.
-/
def topologicalOrder {α} [BEq α] [Hashable α] (tc : TwoComplex α) : Array Nat :=
  let n := tc.base.toGraph.nodes.size
  let order := topo (buildSuccs tc) (buildPreds tc)
  if order.size == n then order else Array.ofFn (n := n) (fun i => i.val)

/--
Full dominator analysis of a TwoComplex:
- dom: dominator bit vectors
- idom: immediate dominator array
- frontier: dominator frontier for each node
- lightcones: (future, past) light cones for each node
-/
structure DominatorAnalysis (α : Type) [BEq α] [Hashable α] where
  tc : TwoComplex α
  preds : Array (Array Nat)
  order : Array Nat
  dom : Array ByteArray
  idom : Array (Option Nat)
  frontier : Array (Array Nat)
  lightcones : Array (Array Nat × Array Nat)

/--
Compute the full dominator analysis for a TwoComplex.
-/
def analyze {α} [BEq α] [Hashable α] (tc : TwoComplex α) : DominatorAnalysis α :=
  let preds := buildPreds tc
  let order := topologicalOrder tc
  let dom := dominators preds order
  let idom := buildIdom preds dom
  let frontier : Array (Array Nat) :=
    Array.ofFn (n := preds.size) (fun i => dominatorFrontier preds dom i.val)
  let lightcones : Array (Array Nat × Array Nat) :=
    Array.ofFn (n := preds.size) (fun i => lightcone dom i.val)
  { tc := tc, preds := preds, order := order, dom := dom,
    idom := idom, frontier := frontier, lightcones := lightcones }

-- Finite executable checks for the dataflow dominator implementation.

private def chainPreds : Array (Array Nat) := #[#[], #[0], #[1]]
private def chainOrder : Array Nat := #[0, 1, 2]

theorem chain_idom_smoke :
    buildIdom chainPreds (dominators chainPreds chainOrder) = #[none, some 0, some 1] := by
  native_decide

private def diamondPreds : Array (Array Nat) := #[#[], #[0], #[0], #[1, 2]]
private def diamondOrder : Array Nat := #[0, 1, 2, 3]

theorem diamond_idom_smoke :
    buildIdom diamondPreds (dominators diamondPreds diamondOrder) =
      #[none, some 0, some 0, some 0] := by
  native_decide

private def multiRootPreds : Array (Array Nat) := #[#[], #[], #[0, 1]]
private def multiRootOrder : Array Nat := #[0, 1, 2]

theorem multi_root_dominance_smoke :
    let dom := dominators multiRootPreds multiRootOrder
    dominates dom 0 1 = false ∧ dominates dom 1 0 = false ∧
      buildIdom multiRootPreds dom = #[none, none, none] := by
  native_decide

end DAG.Dominators

namespace DAG

/-- Backwards-compatible owner alias used by `DAG.Hydrate`. -/
def dominators (preds : Array (Array Nat)) (order : Array Nat) : Array ByteArray :=
  Dominators.dominators preds order

end DAG
