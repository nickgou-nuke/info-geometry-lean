/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Lean
import Std

namespace DAG

universe u

inductive EdgeKind | type | value
  deriving Repr, DecidableEq, BEq, Hashable

structure Graph (α) [BEq α] [Hashable α] where
  nodes     : Array α
  nodeToIdx : Std.HashMap α Nat
  forward   : Array (Array (Nat × EdgeKind))

structure HydratedGraph (α) [BEq α] [Hashable α]
  extends Graph α where
  sccs  : Array (Array Nat)
  sccOf : Array Nat
  dag   : Array (Array Nat)
  preds : Array (Array Nat)
  topo  : Array Nat
  /-- Immediate dominator in the root-to-dependent orientation. -/
  idom : Array (Option Nat)
  /-- Number of strict dominators, equal to the depth in the dominator forest. -/
  idomDepth : Array Nat

variable {α : Type u} [BEq α] [Hashable α]

/-- The empty graph is a constructive base value for graph-building pipelines. -/
def Graph.empty : Graph α where
  nodes := #[]
  nodeToIdx := {}
  forward := #[]

instance : Inhabited (Graph α) where
  default := Graph.empty

/-- An empty hydrated graph, before any SCC or dominance data is computed. -/
def HydratedGraph.empty : HydratedGraph α where
  nodes := #[]
  nodeToIdx := {}
  forward := #[]
  sccs := #[]
  sccOf := #[]
  dag := #[]
  preds := #[]
  topo := #[]
  idom := #[]
  idomDepth := #[]

instance : Inhabited (HydratedGraph α) where
  default := HydratedGraph.empty

instance [Repr α] [BEq α] [Hashable α] :
  Repr (HydratedGraph α) where
  reprPrec h _ :=
    s!"HydratedGraph ⟨nodes := {repr h.toGraph.nodes}, sccs := {repr h.sccs}, topo := {repr h.topo}⟩"

/-- Collect projection head names in an expression.

Uses an explicit worklist and `Std.HashSet Lean.ExprStructEq` visited set so
shared `Lean.Expr` DAG subterms (common in elaborated proof terms and nested
`let`-bindings) are traversed in $O(|V_{\mathrm{DAG}}|)$ time rather than
exponential tree time.
-/
def projHeads (e : Lean.Expr) : Lean.NameSet := Id.run do
  let mut seen : Std.HashSet Lean.ExprStructEq := {}
  let mut stack : List Lean.Expr := [e]
  let mut out : Lean.NameSet := Lean.NameSet.empty
  while !stack.isEmpty do
    let curr := stack.head!
    stack := stack.tail!
    let key : Lean.ExprStructEq := ⟨curr⟩
    if seen.contains key then continue
    seen := seen.insert key
    match curr with
    | .proj s _ body =>
        out := out.insert s
        stack := body :: stack
    | .app f a =>
        stack := f :: a :: stack
    | .lam _ ty body _ =>
        stack := ty :: body :: stack
    | .forallE _ ty body _ =>
        stack := ty :: body :: stack
    | .letE _ ty val body _ =>
        stack := ty :: val :: body :: stack
    | .mdata _ body =>
        stack := body :: stack
    | _ => pure ()
  return out

/-- Collect constant names appearing in an expression. -/
def collectExprConsts (e : Lean.Expr) : Lean.NameSet :=
  let fromConsts :=
    e.foldConsts (init := Lean.NameSet.empty) fun n acc =>
      acc.insert n
  fromConsts.union (projHeads e)

/-- Immediate outgoing edges extracted from a constant. -/
def edgesFromConstantInfo (ci : Lean.ConstantInfo)
    : Array (Lean.Name × EdgeKind) :=
  let typeEdges :=
    (collectExprConsts ci.type).toList.toArray.map
      (fun n => (n, EdgeKind.type))

  let valueEdges :=
    match ci.value? (allowOpaque := true) with
    | none => #[]
    | some v =>
        (collectExprConsts v).toList.toArray.map
          (fun n => (n, EdgeKind.value))

  typeEdges ++ valueEdges

/-- Build a `Graph Name` from an environment, with optional namespace filtering. -/
def buildGraphFromEnv (env : Lean.Environment) (nsPrefix? : Option String := none) : Graph Lean.Name :=
  Id.run do
    let consts := env.constants
    let allNames : Array Lean.Name := 
      match nsPrefix? with
      | none => consts.fold (init := #[]) (fun acc n _ => acc.push n)
      | some p => consts.fold (init := #[]) (fun acc n _ => 
          if (toString n).startsWith p then acc.push n else acc)
    
    let constList : Array Lean.Name := allNames.qsort Lean.Name.lt

    let mut nodeToIdx : Std.HashMap Lean.Name Nat := ({} : Std.HashMap Lean.Name Nat)
    for i in [:constList.size] do
      nodeToIdx := nodeToIdx.insert constList[i]! i

    let mut forward : Array (Array (Nat × EdgeKind)) :=
      Array.replicate constList.size #[]

    for i in [:constList.size] do
      let name := constList[i]!
      match env.find? name with
      | none => pure ()
      | some ci =>
          let edges := edgesFromConstantInfo ci
          for (dep, k) in edges do
            match nodeToIdx.get? dep with
            | none => pure ()
            | some j =>
                forward := forward.modify i (fun arr => arr.push (j, k))
    { nodes := constList, nodeToIdx := nodeToIdx, forward := forward }

end DAG
