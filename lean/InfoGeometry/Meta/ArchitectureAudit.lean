/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Lean
import Std
import DAG.Basic
import DAG.SCC
import InfoGeometry.Meta.Architecture

open Lean Elab Command

namespace InfoGeometry.Meta.ArchitectureAudit

/-- Constant kinds policed as representation-depth surfaces. -/
def isPolicedRepDepthInfo : ConstantInfo → Bool
  | .thmInfo _ | .defnInfo _ | .opaqueInfo _ | .axiomInfo _ => true
  | _ => false

/-- True iff `declName` is a policed declaration carrying `@[rep_depth ...]`.
Non-policed container declarations (`.inductInfo`, `.ctorInfo`, `.recInfo`) do
not terminate representation-depth traversals even if tagged. -/
def isTaggedArchSurface (env : Environment) (declName : Name) : Bool :=
  let queryEnv := env.setExporting false
  match queryEnv.find? declName with
  | some info => isPolicedRepDepthInfo info && (repDepth? env declName).isSome
  | none => false

/-- True iff `declName` lives properly inside the `InfoGeometry.Canonical.` namespace. -/
def isCanonicalSpineDecl (declName : Name) : Bool :=
  (`InfoGeometry.Canonical).isPrefixOf declName && declName != `InfoGeometry.Canonical

private def declNameLeaf : Name → Option String
  | .str _ s => some s
  | _ => none

private def isAlwaysGeneratedLeafName (leaf : String) : Bool :=
  leaf.startsWith "_proof_" ||
  leaf.startsWith "_match_" ||
  leaf.startsWith "_cstage" ||
  leaf.startsWith "_sunpack"

private def isInductiveCompanionLeaf (leaf : String) : Bool :=
  leaf == "mk" ||
  leaf == "sizeOf_spec" ||
  leaf == "inj" ||
  leaf == "injEq" ||
  leaf == "noConfusion" ||
  leaf == "noConfusionType" ||
  leaf == "below" ||
  leaf == "ibelow" ||
  leaf == "brecOn" ||
  leaf == "binductionOn" ||
  leaf == "rec" ||
  leaf == "recOn" ||
  leaf == "casesOn" ||
  leaf == "elim" ||
  leaf == "ctorIdx" ||
  leaf == "toCtorIdx" ||
  leaf == "ctorElim" ||
  leaf == "ctorElimType"

private def isCompanionOfInductiveOrCtor (queryEnv : Environment) (declName : Name) : Bool :=
  match queryEnv.find? declName.getPrefix with
  | some (.inductInfo _) | some (.ctorInfo _) => true
  | _ => false

private def hasGeneratedNameFragment : Name → Bool
  | .anonymous => false
  | .num p _ => hasGeneratedNameFragment p
  | .str p s =>
      s == "_private" ||
      s == "_hyg" ||
      s.contains "._@" ||
      s.startsWith "_proof_" ||
      s.startsWith "_match_" ||
      s.startsWith "_cstage" ||
      hasGeneratedNameFragment p

/--
True iff a declaration should be covered by the strict rep-depth coverage audit.

Scope:
- canonical namespace only;
- public def/theorem surfaces;
- excludes generated/private internals and instance scaffolding.
-/
def isRepDepthCoverageTarget (env : Environment) (declName : Name) (info : ConstantInfo) : Bool :=
  let queryEnv := env.setExporting false
  let leafGenerated :=
    match declNameLeaf declName with
    | some leaf =>
        isAlwaysGeneratedLeafName leaf ||
        (isInductiveCompanionLeaf leaf && isCompanionOfInductiveOrCtor queryEnv declName)
    | none => true
  isDefOrTheoremInfo info &&
    isCanonicalSpineDecl declName &&
    !declName.isInternal &&
    !declName.isInternalDetail &&
    !Lean.isPrivateName declName &&
    !declName.hasMacroScopes &&
    !hasGeneratedNameFragment declName &&
    !leafGenerated &&
    !Lean.isAuxRecursor queryEnv declName &&
    !Lean.isNoConfusion queryEnv declName &&
    !Lean.isSparseCasesOn queryEnv declName &&
    !Lean.Meta.isInstanceCore queryEnv declName &&
    !(queryEnv.isProjectionFn declName) &&
    !(queryEnv.isConstructor declName)

/-- True iff `modName` belongs to an upstream library that cannot depend on `InfoGeometry`. -/
def isExternalUpstreamModule (modName : Name) : Bool :=
  let root := modName.getRoot
  root == `Init || root == `Std || root == `Lean || root == `Batteries ||
    root == `Mathlib || root == `Aesop || root == `Qq || root == `ProofWidgets ||
    root == `ImportGraph || root == `Plausible || root == `Cli

/-- Direct deduplicated constants (and projection struct names) referenced by a declaration's type or value. -/
def directConstDepsOfInfo (info : ConstantInfo) : Array Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut deps : Array Name := #[]
  for (c, _) in DAG.edgesFromConstantInfo info do
    if !seen.contains c then
      seen := seen.insert c
      deps := deps.push c
  return deps

/-- Environment-aware direct dependencies of `info`, resolving primitive `.proj`
nodes to their field projection functions as well as structure types. -/
def directConstDepsOfInfoInEnv (env : Environment) (info : ConstantInfo) : Array Name := Id.run do
  let queryEnv := env.setExporting false
  let mut seen : Std.HashSet Name := {}
  let mut deps : Array Name := #[]
  for (c, _) in DAG.edgesFromConstantInfoInEnv queryEnv info do
    if !seen.contains c then
      seen := seen.insert c
      deps := deps.push c
  return deps

/-- Environment-aware direct dependencies of declaration `declName`, including
resolved `.proj` projection functions and `@[implemented_by ...]` targets. -/
def directConstDepsOfDeclInEnv
    (env : Environment) (declName : Name) (info : ConstantInfo) : Array Name := Id.run do
  let queryEnv := env.setExporting false
  let mut seen : Std.HashSet Name := {}
  let mut deps : Array Name := #[]
  for (c, _) in DAG.directDepsOfDeclInEnv queryEnv declName info do
    if !seen.contains c then
      seen := seen.insert c
      deps := deps.push c
  return deps

/-- Fold over constants declared in the current module without scanning imported modules. -/
def foldCurrentModuleConsts {α : Type}
    (env : Environment) (init : α) (f : α → Name → ConstantInfo → α) : α :=
  if env.constants.stage₁ && env.header.moduleData.isEmpty then
    env.constants.fold f init
  else
    env.constants.foldStage2 f init

/-- Fold over constants in `env.mainModule` plus imported modules selected by `includeModule`. -/
def foldScopedModuleConsts {α : Type}
    (env : Environment)
    (includeModule : Nat → Name → Bool)
    (init : α)
    (f : α → Name → ConstantInfo → α) : α := Id.run do
  let queryEnv := env.setExporting false
  let mut acc := foldCurrentModuleConsts queryEnv init f
  let n := queryEnv.header.moduleData.size
  for i in [:n] do
    let modName := queryEnv.header.moduleNames[i]!
    if includeModule i modName then
      for name in queryEnv.header.moduleData[i]!.constNames do
        if let some info := queryEnv.find? name then
          acc := f acc name info
  return acc

private def computeImportClosure (env : Environment) (directSeed : Array Bool) : Array Bool := Id.run do
  let mods := env.header.moduleData
  let n := mods.size
  let mut modIdxOf : Std.HashMap Name Nat := {}
  for i in [:n] do
    modIdxOf := modIdxOf.insert env.header.moduleNames[i]! i
  -- Reverse the import edges, then propagate from seed modules to every
  -- importer. A DFS with a single `visited` bit is unsound here: a shared
  -- dependency may be encountered while still pending and incorrectly look
  -- like a completed negative result.
  let mut importers : Array (Array Nat) := Array.replicate n #[]
  for importer in [:n] do
    for imp in mods[importer]!.imports do
      if let some dependency := modIdxOf[imp.module]? then
        importers := importers.modify dependency (fun xs => xs.push importer)
  let mut out := directSeed
  let mut queue : Array Nat := #[]
  for i in [:n] do
    if directSeed[i]! then
      queue := queue.push i
  let mut cursor := 0
  while cursor < queue.size do
    let dependency := queue[cursor]!
    cursor := cursor + 1
    for importer in importers[dependency]! do
      if !out[importer]! then
        out := out.set! importer true
        queue := queue.push importer
  return out

/--
Precomputed module-import reachability index for `@[rep_depth ...]` declarations.

Because Lean's module import graph is acyclic, any constant residing in a module `m`
with `canReachTag[m] == false` (all of `Init`, `Std`, `Lean`, `Batteries`, `Mathlib`,
and non-tagged substrate modules) cannot carry `@[rep_depth ...]` or transitively
depend on any `@[rep_depth ...]` declaration.
-/
structure TagReachIndex where
  canImportArch : Array Bool
  canReachTag : Array Bool
  deriving Inhabited

/-- Build `TagReachIndex` in $O(|M| + |E_{\mathrm{mod}}| + |V_{\mathrm{repo}}|)$ time. -/
def TagReachIndex.build (env : Environment) : TagReachIndex := Id.run do
  let n := env.header.moduleData.size
  let mut archSeed := Array.replicate n false
  for i in [:n] do
    let modName := env.header.moduleNames[i]!
    if modName == `InfoGeometry.Meta.Architecture || modName == `InfoGeometry.Meta.ArchitectureAudit then
      archSeed := archSeed.set! i true
  let canImportArch := computeImportClosure env archSeed
  let mut tagSeed := Array.replicate n false
  for i in [:n] do
    let modName := env.header.moduleNames[i]!
    if canImportArch[i]! || !isExternalUpstreamModule modName then
      if env.header.moduleData[i]!.constNames.any (fun c => isTaggedArchSurface env c) then
        tagSeed := tagSeed.set! i true
  let canReachTag := computeImportClosure env tagSeed
  return { canImportArch := canImportArch, canReachTag := canReachTag }

/-- True iff `declName` belongs to `mainModule` or a module that can reach `@[rep_depth ...]`. -/
@[inline] def TagReachIndex.canConstantReachTag
    (idx : TagReachIndex) (env : Environment) (declName : Name) : Bool :=
  match env.getModuleIdxFor? declName with
  | some midx => idx.canReachTag.getD midx.toNat true
  | none => true

private def parsePrefixName? (p : String) : Option Name :=
  let trimmed := if p.endsWith "." then (p.dropEnd 1).toString else p
  let ns :=
    (trimmed.splitOn ".").foldl
      (fun acc part => if part.isEmpty then acc else Name.str acc part)
      .anonymous
  if ns == .anonymous then none else some ns

/-- Transitive closure of constants used by a declaration body or proof term. -/
def transitivelyUsedConstants (env : Environment) (root : Name) : NameSet := Id.run do
  let queryEnv := env.setExporting false
  let mut visited : Std.HashSet Name := {}
  let mut queue : Array Name := #[]
  if let some info := queryEnv.find? root then
    for dep in directConstDepsOfDeclInEnv queryEnv root info do
      if !visited.contains dep then
        visited := visited.insert dep
        queue := queue.push dep
  let mut i := 0
  while i < queue.size do
    let current := queue[i]!
    i := i + 1
    if let some info := queryEnv.find? current then
      for dep in directConstDepsOfDeclInEnv queryEnv current info do
        if !visited.contains dep then
          visited := visited.insert dep
          queue := queue.push dep
  let mut used : NameSet := {}
  for c in queue do
    used := used.insert c
  return used

/-- Early-exit reachability check for target namespace prefixes, pruning external upstream libraries. -/
def reachesNamespacePrefix
    (env : Environment) (root : Name) (targetPrefixes : Array String) : Bool := Id.run do
  let queryEnv := env.setExporting false
  let parsedPrefixes := targetPrefixes.filterMap parsePrefixName?
  let matchesTarget (n : Name) : Bool :=
    parsedPrefixes.any fun ns => ns.isPrefixOf n
  let canExplore (n : Name) : Bool :=
    match queryEnv.getModuleIdxFor? n with
    | some midx =>
        let modName := queryEnv.header.moduleNames.getD midx.toNat .anonymous
        !isExternalUpstreamModule modName
    | none => true
  let mut visited : Std.HashSet Name := ({} : Std.HashSet Name).insert root
  let mut queue : Array Name := #[]
  if let some info := queryEnv.find? root then
    for dep in directConstDepsOfDeclInEnv queryEnv root info do
      if matchesTarget dep then
        return true
      if canExplore dep && !visited.contains dep then
        visited := visited.insert dep
        queue := queue.push dep
  let mut i := 0
  while i < queue.size do
    let curr := queue[i]!
    i := i + 1
    if let some info := queryEnv.find? curr then
      for dep in directConstDepsOfDeclInEnv queryEnv curr info do
        if matchesTarget dep then
          return true
        if canExplore dep && !visited.contains dep then
          visited := visited.insert dep
          queue := queue.push dep
  return false

/-- Direct constants used by a declaration body or proof term. -/
def directlyUsedConstants (env : Environment) (root : Name) : NameSet := Id.run do
  let queryEnv := env.setExporting false
  let mut used : NameSet := {}
  if let some info := queryEnv.find? root then
    for dep in directConstDepsOfDeclInEnv queryEnv root info do
      used := used.insert dep
  return used

/-- Direct dependency adjacency for `TagReachIndex`-eligible constants. -/
def directDependencyMap (env : Environment) : Std.HashMap Name (Array Name) := Id.run do
  let queryEnv := env.setExporting false
  let idx := TagReachIndex.build queryEnv
  foldScopedModuleConsts queryEnv (fun i _ => idx.canReachTag[i]!)
    ({} : Std.HashMap Name (Array Name)) fun acc declName info =>
    acc.insert declName (directConstDepsOfDeclInEnv queryEnv declName info)

/--
Exact linear-time batch computation of nearest `@[rep_depth ...]` descendants
reachable through untagged nodes for a set of roots.

External/non-tag-reaching modules are pruned in $O(1)$ via `TagReachIndex`,
the active untagged subgraph is contracted via iterative Tarjan SCCs (`DAG.tarjan`),
and nearest tagged sets are propagated bottom-up in reverse topological order.
-/
def computeNearestTaggedBatch
    (env : Environment)
    (idx : TagReachIndex)
    (roots : Array Name) : Std.HashMap Name NameSet := Id.run do
  let queryEnv := env.setExporting false
  let mut untaggedNodes : Array Name := #[]
  let mut untaggedIdx : Std.HashMap Name Nat := {}
  let mut untaggedDirectTagged : Array NameSet := #[]
  let mut untaggedEdges : Array (Array (Nat × DAG.EdgeKind)) := #[]

  let mut rootDirectTagged : Array NameSet := Array.replicate roots.size {}
  let mut rootDirectUntagged : Array (Array Nat) := Array.replicate roots.size #[]

  for rIdx in [:roots.size] do
    let r := roots[rIdx]!
    if let some info := queryEnv.find? r then
      let mut directT : NameSet := {}
      let mut directU : Array Nat := #[]
      for dep in directConstDepsOfDeclInEnv queryEnv r info do
        if dep != r && idx.canConstantReachTag queryEnv dep then
          if isTaggedArchSurface queryEnv dep then
            directT := directT.insert dep
          else
            let uId ←
              match untaggedIdx[dep]? with
              | some id => pure id
              | none => do
                  let nodeId := untaggedNodes.size
                  untaggedNodes := untaggedNodes.push dep
                  untaggedIdx := untaggedIdx.insert dep nodeId
                  untaggedDirectTagged := untaggedDirectTagged.push {}
                  untaggedEdges := untaggedEdges.push #[]
                  pure nodeId
            directU := directU.push uId
      rootDirectTagged := rootDirectTagged.set! rIdx directT
      rootDirectUntagged := rootDirectUntagged.set! rIdx directU

  let mut cursor := 0
  while cursor < untaggedNodes.size do
    let u := cursor
    cursor := cursor + 1
    let uName := untaggedNodes[u]!
    if let some info := queryEnv.find? uName then
      let mut uTagged : NameSet := {}
      let mut uAdj : Array (Nat × DAG.EdgeKind) := #[]
      for dep in directConstDepsOfDeclInEnv queryEnv uName info do
        if dep != uName && idx.canConstantReachTag queryEnv dep then
          if isTaggedArchSurface queryEnv dep then
            uTagged := uTagged.insert dep
          else
            let vId ←
              match untaggedIdx[dep]? with
              | some id => pure id
              | none => do
                  let nodeId := untaggedNodes.size
                  untaggedNodes := untaggedNodes.push dep
                  untaggedIdx := untaggedIdx.insert dep nodeId
                  untaggedDirectTagged := untaggedDirectTagged.push {}
                  untaggedEdges := untaggedEdges.push #[]
                  pure nodeId
            uAdj := uAdj.push (vId, DAG.EdgeKind.value)
      untaggedDirectTagged := untaggedDirectTagged.set! u uTagged
      untaggedEdges := untaggedEdges.set! u uAdj

  let comps := DAG.tarjan untaggedEdges
  let mut sccOf : Array Nat := Array.replicate untaggedNodes.size 0
  for compIdx in [:comps.size] do
    for u in comps[compIdx]! do
      sccOf := sccOf.set! u compIdx

  let mut sccTagged : Array NameSet := Array.replicate comps.size {}
  for compIdx in [:comps.size] do
    let mut acc : NameSet := {}
    let mut seenChildSccs : Std.HashSet Nat := {}
    for u in comps[compIdx]! do
      acc := acc.union untaggedDirectTagged[u]!
      for (v, _) in untaggedEdges[u]! do
        let childComp := sccOf[v]!
        if childComp != compIdx && !seenChildSccs.contains childComp then
          seenChildSccs := seenChildSccs.insert childComp
          acc := acc.union sccTagged[childComp]!
    sccTagged := sccTagged.set! compIdx acc

  let mut result : Std.HashMap Name NameSet := {}
  for rIdx in [:roots.size] do
    let r := roots[rIdx]!
    let mut s := rootDirectTagged[rIdx]!
    for u in rootDirectUntagged[rIdx]! do
      s := s.union sccTagged[sccOf[u]!]!
    result := result.insert r (s.erase r)
  return result

/-- Nearest tagged constants reachable from a declaration through untagged nodes. -/
def nearestTaggedDescendants (env : Environment) (root : Name) : NameSet :=
  let queryEnv := env.setExporting false
  let idx := TagReachIndex.build queryEnv
  (computeNearestTaggedBatch queryEnv idx #[root]).getD root {}

/--
Nearest tagged constants reachable from a declaration through untagged nodes,
using a precomputed direct-dependency map.
-/
def nearestTaggedDescendantsFromDeps
    (env : Environment) (directDeps : Std.HashMap Name (Array Name)) (root : Name)
    (initiallyVisited : NameSet := {}) : NameSet := Id.run do
  let queryEnv := env.setExporting false
  let mut nearest : NameSet := {}
  let mut visited : Std.HashSet Name := {}
  for n in initiallyVisited.toList do
    visited := visited.insert n
  visited := visited.insert root
  let mut queue : Array Name := #[]
  for dep in directDeps.getD root #[] do
    if dep != root then
      if isTaggedArchSurface queryEnv dep then
        nearest := nearest.insert dep
      else if directDeps.contains dep && !visited.contains dep then
        visited := visited.insert dep
        queue := queue.push dep
  let mut i := 0
  while i < queue.size do
    let curr := queue[i]!
    i := i + 1
    for dep in directDeps.getD curr #[] do
      if dep != root then
        if isTaggedArchSurface queryEnv dep then
          nearest := nearest.insert dep
        else if directDeps.contains dep && !visited.contains dep then
          visited := visited.insert dep
          queue := queue.push dep
  return nearest.erase root

private partial def nearestTaggedUntaggedMemoAux
    (queryEnv : Environment)
    (directDeps : Std.HashMap Name (Array Name))
    (cacheRef : IO.Ref (Std.HashMap Name NameSet))
    (visiting : NameSet)
    (node : Name) : CoreM (NameSet × Bool) := do
  if let some cached := (← cacheRef.get).get? node then
    return (cached, false)
  if visiting.contains node then
    return ({}, true)
  let nextVisiting := visiting.insert node
  let mut nearest : NameSet := {}
  let mut hitCycle := false
  for dep in directDeps.getD node #[] do
    if isTaggedArchSurface queryEnv dep then
      nearest := nearest.insert dep
    else if directDeps.contains dep then
      let (subNearest, subCycle) ←
        nearestTaggedUntaggedMemoAux queryEnv directDeps cacheRef nextVisiting dep
      nearest := nearest.union subNearest
      if subCycle then
        hitCycle := true
  if !hitCycle then
    cacheRef.modify fun cache => cache.insert node nearest
  return (nearest, hitCycle)

/--
Memoized exact version of `nearestTaggedDescendantsFromDeps` that caches
intermediate untagged nodes across the dependency DAG without rebuilding
`TagReachIndex` or caching cycle-truncated results.
-/
def nearestTaggedDescendantsMemo
    (env : Environment)
    (directDeps : Std.HashMap Name (Array Name))
    (cacheRef : IO.Ref (Std.HashMap Name NameSet))
    (root : Name)
    (visiting : NameSet := {}) : CoreM NameSet := do
  if visiting.isEmpty then
    if let some cached := (← cacheRef.get).get? root then
      return cached
  if visiting.contains root then
    return {}
  let queryEnv := env.setExporting false
  let nextVisiting := visiting.insert root
  let mut nearest : NameSet := {}
  let mut hitCycle := false
  for dep in directDeps.getD root #[] do
    if dep != root then
      if isTaggedArchSurface queryEnv dep then
        nearest := nearest.insert dep
      else if directDeps.contains dep then
        let (subNearest, subCycle) ←
          nearestTaggedUntaggedMemoAux queryEnv directDeps cacheRef nextVisiting dep
        nearest := nearest.union subNearest
        if subCycle then
          hitCycle := true
  if hitCycle || !visiting.isEmpty then
    return nearestTaggedDescendantsFromDeps queryEnv directDeps root visiting
  let cleanNearest := nearest.erase root
  cacheRef.modify fun c => c.insert root cleanNearest
  return cleanNearest

/-- Check architecture violations given an already-computed nearest tagged set. -/
def taggedDependencyViolationsFromSet
    (env : Environment) (declName : Name) (depth : RepDepth)
    (allowComposite : Bool) (deps : NameSet) : Array MessageData := Id.run do
  let queryEnv := env.setExporting false
  let mut out := #[]
  for dep in deps do
    match queryEnv.find? dep with
    | some depInfo =>
        if isPolicedRepDepthInfo depInfo then
          if let some depDepth := repDepth? env dep then
            let d := depth.toNat
            let d' := depDepth.toNat
            if d' > d && !(d == 2 && d' == 3) then
              out := out.push m!"REGRESSION: {declName} (L{d}) depends on {dep} (L{d'}) (possibly transitively through untagged nodes)."
            else if !allowComposite && d' + 1 < d then
              out := out.push m!"WORMHOLE: {declName} (L{d}) depends on {dep} (L{d'}) (possibly transitively through untagged nodes)."
    | none =>
      pure ()
  out

/-- Architecture violations detected from direct and transitive tagged dependencies. -/
def taggedDependencyViolations
    (env : Environment) (declName : Name) (depth : RepDepth) (allowComposite : Bool) : Array MessageData :=
  let deps := nearestTaggedDescendants env declName
  taggedDependencyViolationsFromSet env declName depth allowComposite deps

/--
Architecture violations detected from nearest tagged dependencies, using a
precomputed direct-dependency map.
-/
def taggedDependencyViolationsFromDeps
    (env : Environment) (directDeps : Std.HashMap Name (Array Name))
    (declName : Name) (depth : RepDepth) (allowComposite : Bool) : Array MessageData :=
  let deps := nearestTaggedDescendantsFromDeps env directDeps declName
  taggedDependencyViolationsFromSet env declName depth allowComposite deps

/--
Architecture violations detected from memoized nearest tagged dependencies.
-/
def taggedDependencyViolationsFromDepsM
    (env : Environment) (directDeps : Std.HashMap Name (Array Name))
    (cacheRef : IO.Ref (Std.HashMap Name NameSet))
    (declName : Name) (depth : RepDepth) (allowComposite : Bool) : CoreM (Array MessageData) := do
  let deps ← nearestTaggedDescendantsMemo env directDeps cacheRef declName
  return taggedDependencyViolationsFromSet env declName depth allowComposite deps

private def checkArchitectureTopologyWith
    (scopeLabel? : Option String)
    (includeDecl : Name → Bool)
    (fileOnly : Bool := false) : CoreM Unit := do
  let env ← getEnv
  let queryEnv := env.setExporting false
  let idx := TagReachIndex.build queryEnv
  let mut errors : Array MessageData := #[]

  let collectFn :=
    fun ((taggedAcc, capAcc) : Array (Name × RepDepth) × Array Name)
        (declName : Name) (info : ConstantInfo) =>
      if !includeDecl declName then
        (taggedAcc, capAcc)
      else
        let taggedAcc' :=
          if isPolicedRepDepthInfo info then
            match repDepth? queryEnv declName with
            | some depth => taggedAcc.push (declName, depth)
            | none => taggedAcc
          else
            taggedAcc
        let capAcc' :=
          if capstoneAttr.hasTag queryEnv declName then capAcc.push declName else capAcc
        (taggedAcc', capAcc')

  let (rawTagged, rawCapstones) :=
    if fileOnly then
      foldCurrentModuleConsts queryEnv (#[], #[]) collectFn
    else
      foldScopedModuleConsts queryEnv
        (fun i modName => idx.canImportArch[i]! || !isExternalUpstreamModule modName)
        (#[], #[]) collectFn

  let taggedDecls := rawTagged.qsort (fun a b => toString a.1 < toString b.1)
  let capstones := rawCapstones.qsort (fun a b => toString a < toString b)

  for declName in capstones do
    match queryEnv.find? declName with
    | some info =>
        unless isTheoremInfo info do
          errors := errors.push m!"INVALID CAPSTONE: {declName} is tagged `@[capstone]` but is not a theorem."
        unless (repDepth? queryEnv declName).isSome do
          errors := errors.push m!"INVALID CAPSTONE: {declName} is tagged `@[capstone]` but has no `@[rep_depth ...]`."
    | none =>
        errors := errors.push m!"INVALID CAPSTONE: {declName} is tagged `@[capstone]` but missing from the environment."

  let nearestMap := computeNearestTaggedBatch queryEnv idx (taggedDecls.map Prod.fst)
  for (declName, depth) in taggedDecls do
    let allowComposite := capstoneAttr.hasTag queryEnv declName
    let deps := nearestMap.getD declName {}
    let newErrors := taggedDependencyViolationsFromSet queryEnv declName depth allowComposite deps
    errors := errors ++ newErrors

  let prefixTag := match scopeLabel? with
    | some label => s!" ({label})"
    | none => ""
  if errors.isEmpty then
    logInfo m!"Architecture Audit{prefixTag} PASS: {taggedDecls.size} tagged declarations obey the stable depth grammar."
  else
    for err in errors do
      logError err
    throwError "Architecture Audit{prefixTag} FAILED with {errors.size} violation(s)."

/-- Lean-native architecture audit for the tagged canonical spine. -/
def checkArchitectureTopology : CoreM Unit :=
  -- Strict architecture adjacency is enforced on the canonical spine only.
  -- Other namespaces may carry exploratory tags without gating canonical admission.
  checkArchitectureTopologyWith none fun declName =>
    isCanonicalSpineDecl declName

/-- Scoped Lean-native architecture audit for all tagged declarations under namespace `ns`. -/
def checkArchitectureTopologyForNamespace (ns : Name) : CoreM Unit :=
  checkArchitectureTopologyWith (some s!"namespace {ns}") fun declName =>
    Name.isPrefixOf ns declName

/-- Scoped Lean-native architecture audit for tagged declarations in the current file. -/
def checkArchitectureTopologyForFile : CoreM Unit :=
  checkArchitectureTopologyWith (some "file") (fun _ => true) (fileOnly := true)

/-- Scoped Lean-native architecture audit for a single declaration. -/
def checkArchitectureTopologyForDecl (declName : Name) : CoreM Unit :=
  checkArchitectureTopologyWith (some s!"decl {declName}") (fun n => n == declName)

private def checkRepDepthCoverageWith
    (scopeLabel? : Option String)
    (includeDecl : Name → Bool)
    (fileOnly : Bool := false) : CoreM Unit := do
  let env ← getEnv
  let foldFn :=
    fun ((total, covered, missing) : Nat × Nat × Array Name)
        (declName : Name) (info : ConstantInfo) =>
      if includeDecl declName && isRepDepthCoverageTarget env declName info then
        match repDepth? env declName with
        | some _ => (total + 1, covered + 1, missing)
        | none => (total + 1, covered, missing.push declName)
      else
        (total, covered, missing)
  let (total, covered, rawMissing) :=
    if fileOnly then
      foldCurrentModuleConsts env (0, 0, #[]) foldFn
    else
      foldScopedModuleConsts env (fun _ modName => !isExternalUpstreamModule modName)
        (0, 0, #[]) foldFn
  let missing := rawMissing.qsort (fun a b => toString a < toString b)
  let prefixTag := match scopeLabel? with
    | some label => s!" ({label})"
    | none => ""
  if missing.isEmpty then
    logInfo m!"Rep-Depth Coverage{prefixTag} PASS: {covered}/{total} canonical def/theorem declarations are tagged."
  else
    for declName in missing do
      logError m!"MISSING REP-DEPTH: {declName}"
    throwError
      "Rep-Depth Coverage{prefixTag} FAILED: {missing.size} missing tag(s) out of {total} canonical def/theorem declaration(s)."

/--
Strict rep-depth coverage audit for canonical declaration owners.

This check complements `#audit_architecture`: it reports missing `@[rep_depth ...]`
on canonical public theorem/definition declarations instead of only checking
adjacency among already-tagged declarations.
-/
def checkRepDepthCoverage : CoreM Unit :=
  checkRepDepthCoverageWith none (fun _ => true)

/-- Scoped rep-depth coverage audit for declarations under namespace `ns`. -/
def checkRepDepthCoverageForNamespace (ns : Name) : CoreM Unit :=
  checkRepDepthCoverageWith (some s!"namespace {ns}") fun declName =>
    Name.isPrefixOf ns declName

/-- Scoped rep-depth coverage audit for declarations in the current file. -/
def checkRepDepthCoverageForFile : CoreM Unit :=
  checkRepDepthCoverageWith (some "file") (fun _ => true) (fileOnly := true)

/-- Command entrypoint for the Lean-native architecture audit. -/
elab "#audit_architecture" : command => do
  Command.liftCoreM checkArchitectureTopology

/-- Scoped command entrypoint for auditing a single declaration. -/
elab "#audit_architecture_decl " id:ident : command => do
  let declName ← resolveGlobalConstNoOverload id
  Command.liftCoreM <| checkArchitectureTopologyForDecl declName

/-- Scoped command entrypoint for auditing declarations in the current file. -/
elab "#audit_architecture_file" : command => do
  Command.liftCoreM checkArchitectureTopologyForFile

/-- Scoped command entrypoint for auditing declarations under a namespace. -/
elab "#audit_architecture_namespace " ns:ident : command => do
  Command.liftCoreM <| checkArchitectureTopologyForNamespace ns.getId

/-- Command entrypoint for strict canonical rep-depth coverage auditing. -/
elab "#audit_rep_depth_coverage" : command => do
  Command.liftCoreM checkRepDepthCoverage

/-- Scoped command entrypoint for rep-depth coverage auditing in the current file. -/
elab "#audit_rep_depth_coverage_file" : command => do
  Command.liftCoreM checkRepDepthCoverageForFile

/-- Scoped command entrypoint for rep-depth coverage auditing under a namespace. -/
elab "#audit_rep_depth_coverage_namespace " ns:ident : command => do
  Command.liftCoreM <| checkRepDepthCoverageForNamespace ns.getId

end InfoGeometry.Meta.ArchitectureAudit
