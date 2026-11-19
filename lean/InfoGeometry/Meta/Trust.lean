/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Lean
import Std
import Lean.Util.CollectAxioms
import DAG.Basic
import DAG.SCC
import InfoGeometry.Meta.Admission
import InfoGeometry.Meta.ArchitectureAudit
import InfoGeometry.Meta.RegionPolicy
import InfoGeometry.Meta.Vacuity

open Lean

namespace InfoGeometry.Meta

/-- Legacy explicit forbidden-axiom name list retained for API compatibility. -/
def defaultForbiddenAxioms : List Name := ["admitAx".toName]

/-- Foundational axioms accepted by the repository trust boundary. -/
def permittedFoundationalAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- Return every non-foundational axiom in a collected dependency closure.
`sorryAx` is reported through the separate `hasSorryAx` field so reports can
distinguish explicit `sorry` placeholders from added custom axioms. -/
def forbiddenAxiomsOf (axioms : Array Name) : List Name :=
  axioms.toList.filter fun axiomName =>
    axiomName != ``sorryAx && !permittedFoundationalAxioms.contains axiomName

/-- Repository kinds audited by the first-pass supervisor. -/
def isAuditableDecl : ConstantInfo → Bool
  | .thmInfo _ | .defnInfo _ | .opaqueInfo _ | .axiomInfo _ => true
  | _ => false

/-- Kind label used by the strict audit surface. -/
def constantKindLabel : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

/-- Module defining a declaration, falling back to the main module when unavailable. -/
def moduleNameOf (env : Environment) (declName : Name) : Name :=
  match env.getModuleIdxFor? declName with
  | some idx => env.header.moduleNames[idx.toNat]?.getD env.mainModule
  | none => env.mainModule

private def requiredAttrsMissing
    (policy : PolicySnapshot)
    (env : Environment)
    (declName : Name)
    (region : AdmissionRegion)
    (info : ConstantInfo) : List Name :=
  if region != .protectedRegion then
    []
  else if !isAuditableDecl info then
    []
  else
    (requiredAttrsForRegion policy region).filter fun attr =>
      -- A required attribute is satisfied only by that attribute. A capstone
      -- or vacuity-role tag must not stand in for `rep_depth` (or any future
      -- policy requirement).
      if attr == `rep_depth then
        (repDepth? env declName).isNone
      else if attr == `capstone then
        !capstoneAttr.hasTag env declName
      else if attr == `infrastructure then
        !(infrastructureAttr.hasTag env declName)
      else if attr == `terminal then
        !(terminalAttr.hasTag env declName)
      else if attr == `expository then
        !(expositoryAttr.hasTag env declName)
      else
        true

private def forbiddenRegionKind
    (region : AdmissionRegion)
    (info : ConstantInfo) : Bool :=
  region == .protectedRegion && (info matches .axiomInfo _)

private def repoDepsOfInfo
    (queryEnv : Environment) (declName : Name) (ci : ConstantInfo) : Array Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut deps : Array Name := #[]
  for (c, _) in DAG.edgesFromConstantInfoInEnv queryEnv ci do
    if !seen.contains c then
      seen := seen.insert c
      deps := deps.push c
  if let .inductInfo val := ci then
    for ctor in val.ctors do
      if !seen.contains ctor then
        seen := seen.insert ctor
        deps := deps.push ctor
  if let some implName := Lean.Compiler.getImplementedBy? queryEnv declName then
    if !seen.contains implName then
      seen := seen.insert implName
      deps := deps.push implName
  return deps

private def insertSortedUniqueNames (acc : Array Name) (items : Array Name) : Array Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut out : Array Name := #[]
  for n in acc do
    if !seen.contains n then
      seen := seen.insert n
      out := out.push n
  for n in items do
    if !seen.contains n then
      seen := seen.insert n
      out := out.push n
  return out.qsort Name.quickLt

/--
Collect hard-trust evidence for a batch of declarations with a single shared
DAG pass.

- Axiom closure (`hasSorryAx` / `forbiddenAxioms`): imported declarations read
  pre-computed `.olean` axiom summaries via `Lean.collectAxioms` in $O(1)$
  without crawling Mathlib/Core, while local-module DAG dependencies are
  discovered once and propagated bottom-up across Tarjan SCCs (`DAG.tarjan`).
- Exact `(decl, axiom)` propagation is seeded via `forbiddenSeeds` and
  surfaced through `forbiddenMap`.
- Representation-depth violations share one `TagReachIndex` +
  `computeNearestTaggedBatch` pass across all tagged roots in `declNames`.
-/
def collectHardEvidenceBatch
    (policy : PolicySnapshot)
    (declNames : Array Name) : CoreM (Std.HashMap Name HardEvidence) := do
  let env ← getEnv
  let queryEnv := env.setExporting false

  for declName in declNames do
    if (queryEnv.find? declName).isNone then
      throwError "trust audit cannot find declaration `{declName}`"

  if declNames.isEmpty then
    return {}

  let mut nodes : Array Name := #[]
  let mut nodeIdx : Std.HashMap Name Nat := {}
  let mut edges : Array (Array (Nat × DAG.EdgeKind)) := #[]
  let mut unsafeSeed : Array Bool := #[]
  let mut sorrySeed : Array Bool := #[]
  let mut forbiddenSeeds : Array (Name × Name) := #[]

  let ensureNode := fun (c : Name) (nodes : Array Name) (nodeIdx : Std.HashMap Name Nat)
      (edges : Array (Array (Nat × DAG.EdgeKind))) (unsafeSeed : Array Bool) (sorrySeed : Array Bool) =>
    match nodeIdx[c]? with
    | some id => (id, nodes, nodeIdx, edges, unsafeSeed, sorrySeed)
    | none =>
        let id := nodes.size
        (id, nodes.push c, nodeIdx.insert c id, edges.push #[], unsafeSeed.push false, sorrySeed.push false)

  for declName in declNames do
    let (_, nodes', nodeIdx', edges', unsafeSeed', sorrySeed') :=
      ensureNode declName nodes nodeIdx edges unsafeSeed sorrySeed
    nodes := nodes'
    nodeIdx := nodeIdx'
    edges := edges'
    unsafeSeed := unsafeSeed'
    sorrySeed := sorrySeed'

  let mut cursor := 0
  while cursor < nodes.size do
    let u := cursor
    cursor := cursor + 1
    let uName := nodes[u]!
    if let some ci := queryEnv.find? uName then
      if ci.isUnsafe then
        unsafeSeed := unsafeSeed.set! u true
      match queryEnv.getModuleIdxFor? uName with
      | some midx =>
          let modName := queryEnv.header.moduleNames[midx.toNat]?.getD queryEnv.mainModule
          if isExternalUpstreamModule modName then
            -- Read `.olean` axiom indices via `Lean.collectAxioms` at external boundaries.
            let axs ← Lean.collectAxioms uName
            if axs.contains ``sorryAx then
              sorrySeed := sorrySeed.set! u true
            for ax in forbiddenAxiomsOf axs do
              forbiddenSeeds := forbiddenSeeds.push (uName, ax)
          else
            -- For imported repository modules, seed axioms directly (with `collectAxioms`
            -- fallback only for bodyless opaques) and expand `repoDepsOfInfo` so `unsafe`,
            -- `@[implemented_by ...]`, primitive `.proj` leaks, `sorryAx`, and forbidden
            -- axioms propagate in O(V+E) without O(V^2) `collectAxioms` calls.
            if let .axiomInfo _ := ci then
              if uName == ``sorryAx then
                sorrySeed := sorrySeed.set! u true
              else if !permittedFoundationalAxioms.contains uName then
                forbiddenSeeds := forbiddenSeeds.push (uName, uName)
            else if (ci.value? (allowOpaque := true)).isNone &&
                !(ci matches .inductInfo _ | .ctorInfo _ | .recInfo _ | .quotInfo _) then
              let axs ← Lean.collectAxioms uName
              if axs.contains ``sorryAx then
                sorrySeed := sorrySeed.set! u true
              for ax in forbiddenAxiomsOf axs do
                forbiddenSeeds := forbiddenSeeds.push (uName, ax)
            let mut uAdj : Array (Nat × DAG.EdgeKind) := #[]
            for dep in repoDepsOfInfo queryEnv uName ci do
              let (vId, nodes', nodeIdx', edges', unsafeSeed', sorrySeed') :=
                ensureNode dep nodes nodeIdx edges unsafeSeed sorrySeed
              nodes := nodes'
              nodeIdx := nodeIdx'
              edges := edges'
              unsafeSeed := unsafeSeed'
              sorrySeed := sorrySeed'
              uAdj := uAdj.push (vId, DAG.EdgeKind.value)
            edges := edges.set! u uAdj
      | none =>
          -- Local declaration in `mainModule`: seed local axioms directly and
          -- expand the shared dependency DAG.
          if let .axiomInfo _ := ci then
            if uName == ``sorryAx then
              sorrySeed := sorrySeed.set! u true
            else if !permittedFoundationalAxioms.contains uName then
              forbiddenSeeds := forbiddenSeeds.push (uName, uName)
          let mut uAdj : Array (Nat × DAG.EdgeKind) := #[]
          for dep in repoDepsOfInfo queryEnv uName ci do
            let (vId, nodes', nodeIdx', edges', unsafeSeed', sorrySeed') :=
              ensureNode dep nodes nodeIdx edges unsafeSeed sorrySeed
            nodes := nodes'
            nodeIdx := nodeIdx'
            edges := edges'
            unsafeSeed := unsafeSeed'
            sorrySeed := sorrySeed'
            uAdj := uAdj.push (vId, DAG.EdgeKind.value)
          edges := edges.set! u uAdj

  let mut directForbiddenByNode : Array (Array Name) := Array.replicate nodes.size #[]
  for (seedDecl, axName) in forbiddenSeeds do
    if let some id := nodeIdx[seedDecl]? then
      let cur := directForbiddenByNode[id]!
      if !cur.contains axName then
        directForbiddenByNode := directForbiddenByNode.set! id (cur.push axName)

  let comps := DAG.tarjan edges
  let mut sccOf : Array Nat := Array.replicate nodes.size 0
  for compIdx in [:comps.size] do
    for u in comps[compIdx]! do
      sccOf := sccOf.set! u compIdx

  let mut sccHasSorry : Array Bool := Array.replicate comps.size false
  let mut sccHasUnsafe : Array Bool := Array.replicate comps.size false
  let mut sccForbidden : Array (Array Name) := Array.replicate comps.size #[]

  for compIdx in [:comps.size] do
    let mut compSorry := false
    let mut compUnsafe := false
    let mut compForbidden : Array Name := #[]
    let mut seenChildSccs : Std.HashSet Nat := {}
    for u in comps[compIdx]! do
      if sorrySeed[u]! then
        compSorry := true
      if unsafeSeed[u]! then
        compUnsafe := true
      let df := directForbiddenByNode[u]!
      if !df.isEmpty then
        compForbidden := insertSortedUniqueNames compForbidden df
      for (v, _) in edges[u]! do
        let childComp := sccOf[v]!
        if childComp != compIdx && !seenChildSccs.contains childComp then
          seenChildSccs := seenChildSccs.insert childComp
          if sccHasSorry[childComp]! then
            compSorry := true
          if sccHasUnsafe[childComp]! then
            compUnsafe := true
          let cf := sccForbidden[childComp]!
          if !cf.isEmpty then
            compForbidden := insertSortedUniqueNames compForbidden cf
    sccHasSorry := sccHasSorry.set! compIdx compSorry
    sccHasUnsafe := sccHasUnsafe.set! compIdx compUnsafe
    sccForbidden := sccForbidden.set! compIdx compForbidden

  let mut forbiddenMap : Std.HashMap Name (Array Name) := {}
  for u in [:nodes.size] do
    forbiddenMap := forbiddenMap.insert nodes[u]! sccForbidden[sccOf[u]!]!

  let taggedRoots := declNames.filter fun n => (repDepth? queryEnv n).isSome
  let nearestTaggedMap : Std.HashMap Name NameSet :=
    if taggedRoots.isEmpty then
      {}
    else
      let tagIdx := TagReachIndex.build queryEnv
      computeNearestTaggedBatch queryEnv tagIdx taggedRoots

  let mut out : Std.HashMap Name HardEvidence := {}
  for declName in declNames do
    let some info := queryEnv.find? declName
      | throwError "trust audit cannot find declaration `{declName}`"
    let region := regionOfDecl policy declName
    let missingRequiredAttrs := requiredAttrsMissing policy queryEnv declName region info
    let repDepthViolation :=
      match repDepth? queryEnv declName with
      | some depth =>
          let allowComposite := capstoneAttr.hasTag queryEnv declName
          let deps := nearestTaggedMap.getD declName {}
          !(taggedDependencyViolationsFromSet queryEnv declName depth allowComposite deps).isEmpty
      | none => false
    let comp := sccOf[nodeIdx[declName]!]!
    let forbidden := (forbiddenMap.getD declName #[]).toList
    out := out.insert declName {
      hasSorryAx := sccHasSorry[comp]!
      forbiddenAxioms := forbidden
      unsafeLeakage := sccHasUnsafe[comp]!
      missingRequiredAttrs := missingRequiredAttrs
      repDepthViolation := repDepthViolation
      forbiddenRegionKind := forbiddenRegionKind region info
    }
  return out

/-- Collect hard-trust evidence for a declaration under the current policy. -/
def collectHardEvidence (policy : PolicySnapshot) (declName : Name) : CoreM HardEvidence := do
  let batch ← collectHardEvidenceBatch policy #[declName]
  let some ev := batch[declName]?
    | throwError "trust audit cannot find declaration `{declName}`"
  return ev

end InfoGeometry.Meta
