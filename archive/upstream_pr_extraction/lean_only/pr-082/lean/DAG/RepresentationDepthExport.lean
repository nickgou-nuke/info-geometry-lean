import Lean
import Lean.Data.Json
import DAG.JsonInstances
import InfoGeometry.Meta.Architecture

open Lean
open InfoGeometry.Meta

namespace DAG

structure RepDepthDeclRow where
  name : Name
  module : String
  kind : String
  depth : String
  depthNat : Nat
  sourceDepthNat : Nat
  effectiveSourceDepthNat : Nat
  targetDepthNat : Nat
  directTaggedDepCount : Nat
  closureTaggedDepCount : Nat
  directTaggedDeps : Array Name
  closureTaggedDeps : Array Name
  directDepDepthNats : Array Nat
  closureDepDepthNats : Array Nat
  minDirectDepth? : Option Nat
  maxDirectDepth? : Option Nat
  minClosureDepth? : Option Nat
  maxClosureDepth? : Option Nat
  nearestLowerDirectDepth? : Option Nat
  shallowestLowerDirectDepth? : Option Nat
  nearestLowerClosureDepth? : Option Nat
  shallowestLowerClosureDepth? : Option Nat
  reachesPrevDirect : Bool
  reachesBelowPrevDirect : Bool
  reachesAboveDirect : Bool
  reachesPrevClosure : Bool
  reachesBelowPrevClosure : Bool
  reachesAboveClosure : Bool
  judgment : String
  capstone : Bool
  deriving Repr, ToJson

private def dottedName (s : String) : Name :=
  (s.splitOn ".").foldl (init := Name.anonymous) fun acc part =>
    if part.isEmpty then acc else Name.str acc part

private def moduleNameFor (env : Environment) (declName : Name) : String :=
  match env.getModuleIdxFor? declName with
  | some midx =>
      let mods : List Name := env.header.moduleNames.toList
      let idx : Nat := midx.toNat
      if h : idx < mods.length then
        toString (mods.get ⟨idx, h⟩)
      else
        "<unknown>"
  | none =>
      toString env.mainModule

private def kindString : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .quotInfo _ => "quot"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

private def depthLabel : RepDepth → String
  | .count => "count"
  | .projective => "projective"
  | .operator => "operator"
  | .krein => "krein"
  | .transport => "transport"
  | .thermo => "thermo"

private def sortNames (xs : Array Name) : Array Name :=
  xs.qsort fun a b => toString a < toString b

private def sortNats (xs : Array Nat) : Array Nat :=
  xs.qsort (· < ·)

private def uniqueNames (xs : Array Name) : Array Name := Id.run do
  let mut out := #[]
  for x in xs do
    if !out.contains x then
      out := out.push x
  return sortNames out

private def uniqueNats (xs : Array Nat) : Array Nat := Id.run do
  let mut out := #[]
  for x in xs do
    if !out.contains x then
      out := out.push x
  return sortNats out

private def directTaggedDependencies (env : Environment) (declName : Name) : Array Name := Id.run do
  let mut out := #[]
  for dep in directlyUsedConstants env declName do
    if (repDepth? env dep).isSome then
      out := out.push dep
  return uniqueNames out

private def closureTaggedDependencies (env : Environment) (declName : Name) : Array Name := Id.run do
  let mut out := #[]
  for dep in transitivelyUsedConstants env declName do
    if dep != declName && (repDepth? env dep).isSome then
      out := out.push dep
  return uniqueNames out

private def dependencyDepthNats (env : Environment) (deps : Array Name) : Array Nat :=
  uniqueNats <| deps.foldl (init := #[]) fun acc dep =>
    match repDepth? env dep with
    | some depth => acc.push depth.toNat
    | none => acc

private def minNat? (xs : Array Nat) : Option Nat :=
  if xs.isEmpty then
    none
  else
    some xs[0]!

private def maxNat? (xs : Array Nat) : Option Nat :=
  if xs.isEmpty then
    none
  else
    some xs[xs.size - 1]!

private def lowerDepths (targetDepthNat : Nat) (depths : Array Nat) : Array Nat :=
  sortNats <| depths.filter (fun d => d < targetDepthNat)

private def shallowestLowerDepth? (targetDepthNat : Nat) (depths : Array Nat) : Option Nat :=
  let lowers := lowerDepths targetDepthNat depths
  if lowers.isEmpty then
    none
  else
    some lowers[0]!

private def nearestLowerDepth? (targetDepthNat : Nat) (depths : Array Nat) : Option Nat :=
  let lowers := lowerDepths targetDepthNat depths
  if lowers.isEmpty then
    none
  else
    some lowers[lowers.size - 1]!

private def reachesPrev (targetDepthNat : Nat) (depths : Array Nat) : Bool :=
  targetDepthNat > 0 && depths.contains (targetDepthNat - 1)

private def reachesBelowPrev (targetDepthNat : Nat) (depths : Array Nat) : Bool :=
  depths.any fun d => d + 1 < targetDepthNat

private def reachesAbove (targetDepthNat : Nat) (depths : Array Nat) : Bool :=
  depths.any fun d => targetDepthNat < d

private def judgmentLabel
    (capstone : Bool)
    (targetDepthNat : Nat)
    (directDepDepthNats : Array Nat) : String :=
  let aboveReached := reachesAbove targetDepthNat directDepDepthNats
  let nearestLower? := nearestLowerDepth? targetDepthNat directDepDepthNats
  let deepJump := reachesBelowPrev targetDepthNat directDepDepthNats
  if aboveReached then
    "regression"
  else if capstone then
    "capstone_coherence"
  else match nearestLower? with
    | none => "vertical"
    | some d =>
        if deepJump then
          "wormhole"
        else if d + 1 = targetDepthNat then
          "primitive_translator"
        else
          "wormhole"

private def sourceDepthNatOf (targetDepthNat : Nat) (directDepDepthNats : Array Nat) : Nat :=
  match minNat? directDepDepthNats with
  | some d => Nat.min d targetDepthNat
  | none => targetDepthNat

private def effectiveSourceDepthNatOf (targetDepthNat : Nat) (directDepDepthNats : Array Nat) : Nat :=
  match nearestLowerDepth? targetDepthNat directDepDepthNats with
  | some d => d
  | none => targetDepthNat

private def collectRows (env : Environment) : Array RepDepthDeclRow :=
  env.constants.fold (init := #[]) fun acc declName ci =>
    match repDepth? env declName with
    | some depth =>
        let capstone := capstoneAttr.hasTag env declName
        let targetDepthNat := depth.toNat
        let directTaggedDeps := directTaggedDependencies env declName
        let closureTaggedDeps := closureTaggedDependencies env declName
        let directDepDepthNats := dependencyDepthNats env directTaggedDeps
        let closureDepDepthNats := dependencyDepthNats env closureTaggedDeps
        let sourceDepthNat := sourceDepthNatOf targetDepthNat directDepDepthNats
        let effectiveSourceDepthNat := effectiveSourceDepthNatOf targetDepthNat directDepDepthNats
        acc.push {
          name := declName
          module := moduleNameFor env declName
          kind := kindString ci
          depth := depthLabel depth
          depthNat := targetDepthNat
          sourceDepthNat := sourceDepthNat
          effectiveSourceDepthNat := effectiveSourceDepthNat
          targetDepthNat := targetDepthNat
          directTaggedDepCount := directTaggedDeps.size
          closureTaggedDepCount := closureTaggedDeps.size
          directTaggedDeps := directTaggedDeps
          closureTaggedDeps := closureTaggedDeps
          directDepDepthNats := directDepDepthNats
          closureDepDepthNats := closureDepDepthNats
          minDirectDepth? := minNat? directDepDepthNats
          maxDirectDepth? := maxNat? directDepDepthNats
          minClosureDepth? := minNat? closureDepDepthNats
          maxClosureDepth? := maxNat? closureDepDepthNats
          nearestLowerDirectDepth? := nearestLowerDepth? targetDepthNat directDepDepthNats
          shallowestLowerDirectDepth? := shallowestLowerDepth? targetDepthNat directDepDepthNats
          nearestLowerClosureDepth? := nearestLowerDepth? targetDepthNat closureDepDepthNats
          shallowestLowerClosureDepth? := shallowestLowerDepth? targetDepthNat closureDepDepthNats
          reachesPrevDirect := reachesPrev targetDepthNat directDepDepthNats
          reachesBelowPrevDirect := reachesBelowPrev targetDepthNat directDepDepthNats
          reachesAboveDirect := reachesAbove targetDepthNat directDepDepthNats
          reachesPrevClosure := reachesPrev targetDepthNat closureDepDepthNats
          reachesBelowPrevClosure := reachesBelowPrev targetDepthNat closureDepDepthNats
          reachesAboveClosure := reachesAbove targetDepthNat closureDepDepthNats
          judgment := judgmentLabel capstone targetDepthNat directDepDepthNats
          capstone := capstone
        }
    | none => acc

private def writeOutput (rows : Array RepDepthDeclRow) (outPath : String) : IO Unit := do
  let path := System.FilePath.mk outPath
  match path.parent with
  | some p => IO.FS.createDirAll p
  | none => pure ()
  let payload := Json.mkObj
    [ ("count", toJson rows.size)
    , ("declarations", toJson rows)
    ]
  IO.FS.writeFile path payload.pretty

private def runExport (importModsStr outPath : String) : IO UInt32 := do
  let importMods := importModsStr.splitOn "," |>.map dottedName
  let imports : Array Import := importMods.foldl (init := #[]) fun acc m =>
    acc.push { module := m }
  let env ← importModules imports {} 0
  let rows := (collectRows env).qsort fun a b => toString a.name < toString b.name
  writeOutput rows outPath
  IO.println s!"[RepresentationDepthExport] modules={importModsStr} count={rows.size} wrote {outPath}"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [importModsStr, outPath] =>
      runExport importModsStr outPath
  | _ =>
      IO.eprintln "usage: RepresentationDepthExport <import-module[,module2,...]> <output.json>"
      IO.eprintln "example: lake env lean --run lean/DAG/RepresentationDepthExport.lean InfoGeometry.Canonical.All artifacts/dag/representation-depth-tags.json"
      return 1

end DAG

def main (args : List String) : IO UInt32 :=
  DAG.main args
