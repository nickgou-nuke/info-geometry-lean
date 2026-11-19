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
  let mut stack : Array Lean.Expr := #[e]
  let mut out : Lean.NameSet := Lean.NameSet.empty
  while !stack.isEmpty do
    let curr := stack.back!
    stack := stack.pop
    match curr with
    | .const .. | .bvar .. | .fvar .. | .mvar .. | .sort .. | .lit .. =>
        continue
    | _ => pure ()
    let key : Lean.ExprStructEq := ⟨curr⟩
    if seen.contains key then continue
    seen := seen.insert key
    match curr with
    | .proj s _ body =>
        out := out.insert s
        stack := stack.push body
    | .app f a =>
        stack := stack.push a
        stack := stack.push f
    | .lam _ ty body _ =>
        stack := stack.push body
        stack := stack.push ty
    | .forallE _ ty body _ =>
        stack := stack.push body
        stack := stack.push ty
    | .letE _ ty val body _ =>
        stack := stack.push body
        stack := stack.push val
        stack := stack.push ty
    | .mdata _ body =>
        stack := stack.push body
    | _ => pure ()
  return out

/-- Collect constant names (including `.proj` struct names) occurring in an expression.

Lean's `Expr.getUsedConstantsAsSet` already traverses `Expr` via pointer equality
(`PtrSet`) and inserts structure type names for `.proj` nodes, avoiding a redundant
second pass. -/
def collectExprConsts (e : Lean.Expr) : Lean.NameSet :=
  e.getUsedConstantsAsSet

/-- Collect resolved structure projection function names for `.proj s idx body`
nodes appearing in `e`, looking up `Lean.getStructureInfo? env s`. -/
def projFnTargetsInEnv (env : Lean.Environment) (e : Lean.Expr) : Lean.NameSet := Id.run do
  let queryEnv := env.setExporting false
  let mut seen : Std.HashSet Lean.ExprStructEq := {}
  let mut stack : Array Lean.Expr := #[e]
  let mut out : Lean.NameSet := Lean.NameSet.empty
  while !stack.isEmpty do
    let curr := stack.back!
    stack := stack.pop
    match curr with
    | .const .. | .bvar .. | .fvar .. | .mvar .. | .sort .. | .lit .. =>
        continue
    | _ => pure ()
    let key : Lean.ExprStructEq := ⟨curr⟩
    if seen.contains key then continue
    seen := seen.insert key
    match curr with
    | .proj s idx body =>
        if let some sinfo := Lean.getStructureInfo? queryEnv s then
          if let some projFn := sinfo.getProjFn? idx then
            out := out.insert projFn
        stack := stack.push body
    | .app f a =>
        stack := stack.push a
        stack := stack.push f
    | .lam _ ty body _ =>
        stack := stack.push body
        stack := stack.push ty
    | .forallE _ ty body _ =>
        stack := stack.push body
        stack := stack.push ty
    | .letE _ ty val body _ =>
        stack := stack.push body
        stack := stack.push val
        stack := stack.push ty
    | .mdata _ body =>
        stack := stack.push body
    | _ => pure ()
  return out

/-- Collect constant names in `e`, resolving `.proj s idx _` nodes to both `s`
and the field projection function `(getStructureInfo? env s).bind (·.getProjFn? idx)`. -/
def collectExprConstsInEnv (env : Lean.Environment) (e : Lean.Expr) : Lean.NameSet :=
  let queryEnv := env.setExporting false
  let base := e.getUsedConstantsAsSet
  let hasStructTarget := base.any fun c => (Lean.getStructureInfo? queryEnv c).isSome
  if hasStructTarget then
    base.union (projFnTargetsInEnv queryEnv e)
  else
    base

/-- Sorted deduplicated constants in `e`, including resolved `.proj` projection functions. -/
private def usedConstantsWithProjFnsInEnv
    (queryEnv : Lean.Environment) (e : Lean.Expr) : Array Lean.Name := Id.run do
  let base := e.getUsedConstants
  let hasStructTarget := base.any fun c => (Lean.getStructureInfo? queryEnv c).isSome
  if !hasStructTarget then
    return base.qsort Lean.Name.quickLt
  let projFns := projFnTargetsInEnv queryEnv e
  if projFns.isEmpty then
    return base.qsort Lean.Name.quickLt
  let mut seen : Std.HashSet Lean.Name := {}
  for c in base do
    seen := seen.insert c
  let mut out := Array.mkEmpty (base.size + projFns.size)
  out := out ++ base
  for p in projFns do
    if !seen.contains p then
      seen := seen.insert p
      out := out.push p
  return out.qsort Lean.Name.quickLt

/-- Immediate outgoing edges extracted from a constant using C++ `PtrSet` traversal. -/
def edgesFromConstantInfo (ci : Lean.ConstantInfo)
    : Array (Lean.Name × EdgeKind) := Id.run do
  let typeNames := ci.type.getUsedConstants.qsort Lean.Name.quickLt
  let valNames :=
    match ci.value? (allowOpaque := true) with
    | none => #[]
    | some v => v.getUsedConstants.qsort Lean.Name.quickLt
  let mut out : Array (Lean.Name × EdgeKind) :=
    Array.mkEmpty (typeNames.size + valNames.size)
  for n in typeNames do
    out := out.push (n, EdgeKind.type)
  for n in valNames do
    out := out.push (n, EdgeKind.value)
  return out

/-- Immediate outgoing edges extracted from a constant in `env`, resolving
primitive `.proj` nodes to their structure field projection functions as well as
the structure type itself. -/
def edgesFromConstantInfoInEnv (env : Lean.Environment) (ci : Lean.ConstantInfo)
    : Array (Lean.Name × EdgeKind) := Id.run do
  let queryEnv := env.setExporting false
  let typeNames := usedConstantsWithProjFnsInEnv queryEnv ci.type
  let valNames :=
    match ci.value? (allowOpaque := true) with
    | none => #[]
    | some v => usedConstantsWithProjFnsInEnv queryEnv v
  let mut out : Array (Lean.Name × EdgeKind) :=
    Array.mkEmpty (typeNames.size + valNames.size)
  for n in typeNames do
    out := out.push (n, EdgeKind.type)
  for n in valNames do
    out := out.push (n, EdgeKind.value)
  return out

/-- Immediate outgoing edges extracted from declaration `declName` in `env`,
resolving primitive `.proj` field projections and `@[implemented_by ...]` targets. -/
def directDepsOfDeclInEnv (env : Lean.Environment) (declName : Lean.Name) (ci : Lean.ConstantInfo)
    : Array (Lean.Name × EdgeKind) := Id.run do
  let queryEnv := env.setExporting false
  let base := edgesFromConstantInfoInEnv queryEnv ci
  match Lean.Compiler.getImplementedBy? queryEnv declName with
  | some implName =>
      if implName != declName && !base.any (fun (n, k) => n == implName && k == EdgeKind.value) then
        return base.push (implName, EdgeKind.value)
      else
        return base
  | none => return base

private def parseNamespacePrefix (p : String) : Lean.Name × Bool :=
  let strictChild := p.endsWith "."
  let trimmed := if strictChild then (p.dropEnd 1).toString else p
  let nsName :=
    (trimmed.splitOn ".").foldl
      (fun acc part => if part.isEmpty then acc else Lean.Name.str acc part)
      .anonymous
  (nsName, strictChild)

private def dedupSortedNames (xs : Array Lean.Name) : Array Lean.Name := Id.run do
  if xs.size ≤ 1 then return xs
  let mut out : Array Lean.Name := Array.mkEmpty xs.size
  let mut prev : Option Lean.Name := none
  for x in xs do
    if prev != some x then
      out := out.push x
      prev := some x
  return out

private def isUpstreamExternalRoot (root : Lean.Name) : Bool :=
  root == `Init || root == `Std || root == `Lean || root == `Batteries ||
    root == `Mathlib || root == `Aesop || root == `Qq || root == `ProofWidgets ||
    root == `ImportGraph || root == `Plausible || root == `Cli

/-- Build a `Graph Name` from an environment, with optional namespace filtering. -/
def buildGraphFromEnv (env : Lean.Environment) (nsPrefix? : Option String := none) : Graph Lean.Name :=
  Id.run do
    let queryEnv := env.setExporting false
    let consts := queryEnv.constants
    let allNames : Array Lean.Name :=
      match nsPrefix? with
      | none | some "" =>
          consts.fold (init := #[]) (fun acc n _ => acc.push n)
      | some p =>
          let (nsName, strictChild) := parseNamespacePrefix p
          let pRoot := nsName.getRoot
          let rootMightMatch := fun (r : Lean.Name) =>
            r == pRoot || pRoot.isPrefixOf r || r.isPrefixOf pRoot
          let matchesPrefix := fun (n : Lean.Name) =>
            if n == .anonymous || nsName == .anonymous then
              false
            else if strictChild then
              nsName.isPrefixOf n && n != nsName
            else
              nsName.isPrefixOf n
          if consts.stage₁ && queryEnv.header.moduleData.isEmpty then
            consts.fold (init := #[]) fun acc n _ =>
              if matchesPrefix n then acc.push n else acc
          else
            let localNames :=
              consts.foldStage2 (fun acc n _ =>
                if matchesPrefix n then acc.push n else acc
              ) #[]
            Id.run do
              let mut acc := localNames
              let modCount := queryEnv.header.moduleData.size
              for idx in [:modCount] do
                let modName := queryEnv.header.moduleNames[idx]?.getD .anonymous
                let modRoot := modName.getRoot
                if !isUpstreamExternalRoot modRoot || rootMightMatch modRoot then
                  for name in queryEnv.header.moduleData[idx]!.constNames do
                    if matchesPrefix name && (queryEnv.find? name).isSome then
                      acc := acc.push name
              return acc

    let constList : Array Lean.Name := dedupSortedNames (allNames.qsort Lean.Name.lt)

    let mut nodeToIdx : Std.HashMap Lean.Name Nat := ({} : Std.HashMap Lean.Name Nat)
    for i in [:constList.size] do
      nodeToIdx := nodeToIdx.insert constList[i]! i

    let mut forward : Array (Array (Nat × EdgeKind)) :=
      Array.replicate constList.size #[]

    for i in [:constList.size] do
      let name := constList[i]!
      match queryEnv.find? name with
      | none => pure ()
      | some ci =>
          let mut seenEdges : Std.HashSet (Nat × EdgeKind) := {}
          let mut adj : Array (Nat × EdgeKind) := #[]
          for (dep, k) in directDepsOfDeclInEnv queryEnv name ci do
            if let some j := nodeToIdx[dep]? then
              if !seenEdges.contains (j, k) then
                seenEdges := seenEdges.insert (j, k)
                adj := adj.push (j, k)
          forward := forward.set! i adj
    { nodes := constList, nodeToIdx := nodeToIdx, forward := forward }

end DAG
