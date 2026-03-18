import Lean
import Std
import DAG.Basic
import DAG.Util
import DAG.JsonInstances
import DAG.Hydrate
import DAG.Analysis
import InfoGeometry.Canonical.SpineAttributes

open Lean
open Lean.Parser
open Lean.Elab
open Lean.Elab.Frontend
open Lean.Meta

namespace DAG

/-- One top‑level command slice + constants produced. -/
inductive ScopeKind where
  | namespace
  | section
  deriving BEq, Inhabited, ToJson, FromJson

structure ScopeFrame where
  kind : ScopeKind
  name : Name
  deriving BEq, Inhabited, ToJson, FromJson

/-- A categorical morphism representing a proof step or state transition. -/
structure TacticMorphism where
  tacticSyntax : String
  beforeState  : Array String
  afterState   : Array String
deriving Repr, ToJson, FromJson, Inhabited

/--
One top-level command slice plus the declarations it produces.

`primaryProduces` records stable, user-authored declarations.
`auxProduces` records generated/unstable declarations such as matchers,
equation lemmas, and private auxiliaries.

The derived view `blk.produces` preserves the legacy flat projection.
-/
structure Block where
  idx             : Nat
  stableId        : String
  startUtf8       : String.Pos.Raw
  stopUtf8        : String.Pos.Raw
  startPos        : Position
  stopPos         : Position
  text            : String
  scopes          : Array ScopeFrame
  primaryProduces : Array Name
  auxProduces     : Array Name
  primarySpineTags : Array (Name × Array String)
  spineTags       : Array String
  affects         : Array Name
  morphisms       : Array TacticMorphism
  docStrings      : Array String
  typeStrings     : Array String
deriving Inhabited

namespace Block

/-- Legacy flat view of declarations produced by a block. -/
def produces (blk : Block) : Array Name :=
  (blk.primaryProduces ++ blk.auxProduces).qsort Name.lt

end Block

/-- Deterministic block identifier within a file, based on the command span. -/
def mkStableBlockId (startUtf8 stopUtf8 : String.Pos.Raw) : String :=
  s!"block:{startUtf8.byteIdx}-{stopUtf8.byteIdx}"

/-- Split declarations into stable primary outputs and generated auxiliaries. -/
def classifyProducedDecls (decls : Array Name) : Array Name × Array Name := Id.run do
  let mut primaryDecls : Array Name := #[]
  let mut auxDecls : Array Name := #[]
  for n in decls do
    if isGeneratedOrUnstableName n then
      auxDecls := auxDecls.push n
    else
      primaryDecls := primaryDecls.push n
  (primaryDecls, auxDecls)

/-- Semantic declarations authored directly by source blocks. -/
def primaryDeclSet (blocks : Array Block) : Std.HashSet Name :=
  Id.run do
    let mut out : Std.HashSet Name := {}
    for blk in blocks do
      for n in blk.primaryProduces do
        out := out.insert n
    out

/-- Snapshot semantic spine tags for primary declarations produced by a block. -/
def collectPrimarySpineTags (env : Environment) (primaryDecls : Array Name) :
    Array (Name × Array String) :=
  primaryDecls.map fun n => (n, InfoGeometry.Canonical.spineTagStringsOf env n)

/-- Deduplicated block-level summary of per-primary semantic spine tags. -/
def summarizeSpineTags (primarySpineTags : Array (Name × Array String)) : Array String := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut out : Array String := #[]
  for (_, tags) in primarySpineTags do
    for tag in tags do
      if !seen.contains tag then
        seen := seen.insert tag
        out := out.push tag
  out

private def toJsonPrimarySpineTags (primarySpineTags : Array (Name × Array String)) : Json :=
  Json.arr <| primarySpineTags.map fun (declName, tags) =>
    Json.mkObj [("decl", toJson declName), ("tags", toJson tags)]

private def fromJsonPrimarySpineTags? (j : Json) : Except String (Array (Name × Array String)) := do
  let entries ← j.getArr?
  let mut out : Array (Name × Array String) := #[]
  for entry in entries do
    let declName ← entry.getObjValAs? Name "decl"
    let tags ← entry.getObjValAs? (Array String) "tags"
    out := out.push (declName, tags)
  pure out

instance : ToJson Block where
  toJson blk :=
    Json.mkObj
      [ ("idx", toJson blk.idx)
      , ("stableId", toJson blk.stableId)
      , ("startUtf8", toJson blk.startUtf8)
      , ("stopUtf8", toJson blk.stopUtf8)
      , ("startPos", toJson blk.startPos)
      , ("stopPos", toJson blk.stopPos)
      , ("text", toJson blk.text)
      , ("scopes", toJson blk.scopes)
      , ("primaryProduces", toJson blk.primaryProduces)
      , ("auxProduces", toJson blk.auxProduces)
      , ("primarySpineTags", toJsonPrimarySpineTags blk.primarySpineTags)
      , ("spineTags", toJson blk.spineTags)
      , ("produces", toJson blk.produces)
      , ("affects", toJson blk.affects)
      , ("morphisms", toJson blk.morphisms)
      , ("docStrings", toJson blk.docStrings)
      , ("typeStrings", toJson blk.typeStrings)
      ]

instance : FromJson Block where
  fromJson? j := do
    let idx ← j.getObjValAs? Nat "idx"
    let startUtf8 ← j.getObjValAs? String.Pos.Raw "startUtf8"
    let stopUtf8 ← j.getObjValAs? String.Pos.Raw "stopUtf8"
    let stableId :=
      match j.getObjValAs? String "stableId" with
      | .ok s => s
      | .error _ => mkStableBlockId startUtf8 stopUtf8
    let startPos ← j.getObjValAs? Position "startPos"
    let stopPos ← j.getObjValAs? Position "stopPos"
    let text ← j.getObjValAs? String "text"
    let scopes ← j.getObjValAs? (Array ScopeFrame) "scopes"
    let legacyProduces :=
      match j.getObjValAs? (Array Name) "produces" with
      | .ok xs => xs
      | .error _ => #[]
    let primaryProduces :=
      match j.getObjValAs? (Array Name) "primaryProduces" with
      | .ok xs => xs
      | .error _ => legacyProduces.filter (fun n => !isGeneratedOrUnstableName n)
    let auxProduces :=
      match j.getObjValAs? (Array Name) "auxProduces" with
      | .ok xs => xs
      | .error _ => legacyProduces.filter isGeneratedOrUnstableName
    let primarySpineTags :=
      match j.getObjVal? "primarySpineTags" with
      | .ok raw => fromJsonPrimarySpineTags? raw
      | .error _ => .ok (primaryProduces.map fun n => (n, #[]))
    let primarySpineTags ← primarySpineTags
    let spineTags :=
      match j.getObjValAs? (Array String) "spineTags" with
      | .ok xs => xs
      | .error _ => summarizeSpineTags primarySpineTags
    let affects ← j.getObjValAs? (Array Name) "affects"
    let morphisms ← j.getObjValAs? (Array TacticMorphism) "morphisms"
    let docStrings ← j.getObjValAs? (Array String) "docStrings"
    let typeStrings ← j.getObjValAs? (Array String) "typeStrings"
    pure {
      idx := idx
      stableId := stableId
      startUtf8 := startUtf8
      stopUtf8 := stopUtf8
      startPos := startPos
      stopPos := stopPos
      text := text
      scopes := scopes
      primaryProduces := primaryProduces
      auxProduces := auxProduces
      primarySpineTags := primarySpineTags
      spineTags := spineTags
      affects := affects
      morphisms := morphisms
      docStrings := docStrings
      typeStrings := typeStrings
    }

/-- Export result for a file. -/
structure Export where
  file       : String
  header     : String
  blocks     : Array Block
  decls      : Array Name
  producer   : Array Nat
  graph      : DAG.Graph Name
  blockGraph : DAG.Graph Nat
  skeletonMap: Array (Name × Nat)
deriving ToJson, FromJson

/-- Walks the InfoTree to collect fully elaborated constants. -/
def collectInfoDeps (t : InfoTree) (acc : NameSet) : NameSet :=
  t.foldInfo (fun _ctx info acc =>
    match info with
    | .ofTermInfo ti =>
        ti.expr.foldConsts (init := acc) (fun n a => a.insert n)
    | _ => acc
  ) acc

/-- Walk an `InfoTree` and extract tactic state transitions as pure morphisms using ppGoal. -/
partial def extractMorphisms (t : InfoTree) (ctx? : Option ContextInfo := none) : IO (Array TacticMorphism) := do
  let mut ms : Array TacticMorphism := #[]

  match t with
  | .context p t =>
      ms := ms ++ (← extractMorphisms t (p.mergeIntoOuter? ctx?))

  | .node info children =>
      let ctx? := info.updateContext? ctx?
      for c in children do
        ms := ms ++ (← extractMorphisms c ctx?)

      match info with
      | .ofTacticInfo ti =>
          match ctx? with
          | none => pure ()
          | some ctx =>
              let morph ← ctx.runMetaM (lctx := (default : LocalContext)) do
                let getStates (mctx : MetavarContext) (goals : List MVarId) : MetaM (Array String) :=
                  withMCtx mctx do
                    let mut out : Array String := #[]
                    for g in goals do
                      if (← g.isAssigned) then continue
                      let goalStr ← Meta.ppGoal g
                      out := out.push goalStr.pretty
                    pure out

                pure {
                  tacticSyntax := ti.stx.reprint.getD ""
                  beforeState  := (← getStates ti.mctxBefore ti.goalsBefore)
                  afterState   := (← getStates ti.mctxAfter  ti.goalsAfter)
                }

              ms := ms.push morph
      | _ => pure ()

  | .hole _ => pure ()

  pure ms

/-- Build graph restricted to decls. -/
def buildGraphFromEnvOn (env : Environment) (decls : Array Name) : DAG.Graph Name :=
  Id.run do
    let decls := decls.qsort Name.lt
    let mut nodeToIdx : Std.HashMap Name Nat := {}
    for i in [:decls.size] do
      nodeToIdx := nodeToIdx.insert decls[i]! i
    let mut forward : Array (Array (Nat × DAG.EdgeKind)) :=
      Array.replicate decls.size #[]
    for i in [:decls.size] do
      let n := decls[i]!
      match env.find? n with
      | none => pure ()
      | some ci =>
        let edges := edgesFromConstantInfo ci
        for (dep, k) in edges do
          match nodeToIdx.get? dep with
          | none => pure ()
          | some j => forward := forward.modify i (·.push (j, k))
    { nodes := decls, nodeToIdx := nodeToIdx, forward := forward }

/-- Name → producing block index map. -/
def producerMap (decls : Array Name) (producer : Array Nat) : Std.HashMap Name Nat :=
  Id.run do
    let mut m : Std.HashMap Name Nat := {}
    let n := Nat.min decls.size producer.size
    for i in [:n] do
      m := m.insert decls[i]! producer[i]!
    m

/-- Coarse block graph induced by const deps. -/
def buildBlockGraph (constG : DAG.Graph Name) (prod : Std.HashMap Name Nat) (numBlocks : Nat) : DAG.Graph Nat :=
  Id.run do
    let nodes := Array.range numBlocks
    let mut nodeToIdx : Std.HashMap Nat Nat := {}
    for i in [:nodes.size] do
      nodeToIdx := nodeToIdx.insert nodes[i]! i

    let mut forward : Array (Array (Nat × DAG.EdgeKind)) := Array.replicate numBlocks #[]
    let mut seen : Std.HashSet (Nat × Nat × DAG.EdgeKind) := {}

    for ui in [:constG.nodes.size] do
      let u := constG.nodes[ui]!
      let some bu := prod.get? u | continue
      for (vj, k) in constG.forward[ui]! do
        let v := constG.nodes[vj]!
        let some bv := prod.get? v | continue
        if bu != bv && !seen.contains (bu, bv, k) then
          seen := seen.insert (bu, bv, k)
          forward := forward.modify bu (·.push (bv, k))

    { nodes := nodes, nodeToIdx := nodeToIdx, forward := forward }

/-- Given an export and a target constant, compute the set of block
    indices needed to produce that constant. -/
def minimalBlocksFor (e : Export) (target : Name) : Array Nat :=
  match e.graph.nodeToIdx.get? target with
  | none => #[]
  | some startIdx => Id.run do
      let mut visited : Std.HashSet Nat := {}
      let mut stack := #[startIdx]
      while stack.size > 0 do
        let i := stack.back!
        stack := stack.pop
        if !visited.contains i then
          visited := visited.insert i
          for (j, _) in e.graph.forward[i]! do
            if !visited.contains j then
              stack := stack.push j
      let prodMap := producerMap e.decls e.producer
      let mut blocks : Std.HashSet Nat := {}
      for i in visited.toList do
        let n := e.graph.nodes[i]!
        match prodMap.get? n with
        | some b => blocks := blocks.insert b
        | none   => ()
      blocks.toArray.qsort (· < ·)

/-- run the frontend, invoking `hook` after each command. -/
partial def runCommands (hook : FrontendM Unit) : FrontendM Unit := do
  let done ← Frontend.processCommand
  hook
  unless done do
    runCommands hook

/-- Export a file. -/
def exportFile (file : System.FilePath) (opts : Options := {}) : IO Export := do
  Lean.initSearchPath (← Lean.findSysroot)
  let opts := Elab.async.setIfNotSet opts false
  let input ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext input file.toString
  let (headerStx, parserState, msgs) ← Parser.parseHeader inputCtx
  let headerText : String :=
    String.Pos.Raw.extract inputCtx.inputString ⟨0⟩ parserState.pos
  let (env0, msgs) ← Elab.processHeader headerStx opts msgs inputCtx 0
  let cmdState0 := Command.mkState env0 msgs opts
  let initSt : Frontend.State :=
    { commandState := cmdState0
      parserState := parserState
      cmdPos := parserState.pos
      commands := #[] }
  let ctx : Frontend.Context := { inputCtx := inputCtx }
  let baseSeen : NameSet :=
    env0.constants.fold (init := ({} : NameSet)) (fun s n _ => s.insert n)
  let seenRef : IO.Ref NameSet ← IO.mkRef baseSeen
  let declsRef  : IO.Ref (Array Name)  ← IO.mkRef #[]
  let prodRef   : IO.Ref (Array Nat)   ← IO.mkRef #[]
  let blocksRef : IO.Ref (Array Block) ← IO.mkRef #[]
  let scopeRef  : IO.Ref (List ScopeFrame) ← IO.mkRef []
  let treesRef  : IO.Ref Nat           ← IO.mkRef 0

  let hook : FrontendM Unit := do
    let st ← get
    let some stx := st.commands.back? | return
    let some r := stx.getRangeWithTrailing? | return

    -- update scope stack
    match stx with
    | `(namespace $id:ident) =>
        scopeRef.modify fun lst => { kind := ScopeKind.namespace, name := id.getId } :: lst
    | `(section) =>
        scopeRef.modify fun lst => { kind := ScopeKind.section, name := Name.anonymous } :: lst
    | `(section $id:ident) =>
        scopeRef.modify fun lst => { kind := ScopeKind.section, name := id.getId } :: lst
    | `(end $id?) =>
        scopeRef.modify fun | [] => [] | _ :: xs => xs
    | _ => pure ()

    if r.stop.byteIdx ≤ r.start.byteIdx then return

    let text := String.Pos.Raw.extract inputCtx.inputString r.start r.stop
    if text.trimAscii.isEmpty then return

    let blocks ← blocksRef.get
    let blockIdx := blocks.size
    let startPos := inputCtx.fileMap.toPosition r.start
    let stopPos := inputCtx.fileMap.toPosition r.stop
    let after := st.commandState
    let seen ← seenRef.get
    let (newDecls0, seen') :=
      after.env.constants.foldStage2
        (fun (acc : Array Name × NameSet) n _ =>
          let (arr, s) := acc
          if s.contains n then
            (arr, s)
          else
            let s := s.insert n
            (arr.push n, s))
        (#[], seen)
    seenRef.set seen'
    let newDecls := newDecls0.qsort Name.lt
    if newDecls.size > 0 then
      declsRef.modify (· ++ newDecls)
      prodRef.modify  (· ++ Array.replicate newDecls.size blockIdx)

    let (primaryDecls, auxDecls) := classifyProducedDecls newDecls
    let primarySpineTags := collectPrimarySpineTags after.env primaryDecls
    let spineTags := summarizeSpineTags primarySpineTags

    -- Semantic deps + morphisms via InfoTree: only process new trees since last command
    let trees := after.infoState.trees
    let prev ← treesRef.get
    let now := trees.size
    treesRef.set now

    let mut newTrees : Array InfoTree := #[]
    for i in [prev:now] do
      newTrees := newTrees.push trees[i]!

    let mut affectsSet : NameSet := {}
    for t in newTrees do
      affectsSet := collectInfoDeps t affectsSet

    let affectsSetClean := newDecls.foldl (fun s n => s.erase n) affectsSet
    let affects := affectsSetClean.toArray.qsort Name.lt

    let mut ms : Array TacticMorphism := #[]
    for t in newTrees do
      ms := ms ++ (← extractMorphisms t)

    let mut docStrings : Array String := #[]
    let mut typeStrings : Array String := #[]
    for n in newDecls do
      let doc ← match ← Lean.findDocString? after.env n with
                | some d => pure d
                | none => pure ""
      docStrings := docStrings.push doc
      let tstr ← match after.env.find? n with
                 | some ci => pure (toString ci.type)
                 | none => pure ""
      typeStrings := typeStrings.push tstr

    let scopes := (← scopeRef.get).reverse.toArray
    let blk : Block :=
      { idx := blockIdx
        stableId := mkStableBlockId r.start r.stop
        startUtf8 := r.start
        stopUtf8 := r.stop
        startPos := startPos
        stopPos := stopPos
        text := text
        scopes := scopes
        primaryProduces := primaryDecls
        auxProduces := auxDecls
        primarySpineTags := primarySpineTags
        spineTags := spineTags
        affects := affects
        morphisms := ms
        docStrings := docStrings
        typeStrings := typeStrings }
    blocksRef.set (blocks.push blk)

  let (_u, stFinal) ← ((runCommands hook).run ctx).run initSt
  let blocks   ← blocksRef.get
  let decls    ← declsRef.get
  let producer ← prodRef.get
  let graph := buildGraphFromEnvOn stFinal.commandState.env decls
  let prodMap := producerMap decls producer
  let blockGraph := buildBlockGraph graph prodMap blocks.size

  -- True Skeleton extraction
  let hydratedG := DAG.hydrate graph
  let skelPairs := DAG.extractTheorySkeletonWithPreferred hydratedG (primaryDeclSet blocks) 1
  let mut skelMap : Array (Name × Nat) := #[]
  for i in [:skelPairs.size] do
    let (n, _, rank) := skelPairs[i]!
    skelMap := skelMap.push (n, rank)

  pure {
    file := file.toString,
    header := headerText,
    blocks := blocks,
    decls := decls,
    producer := producer,
    graph := graph,
    blockGraph := blockGraph,
    skeletonMap := skelMap
  }

def isScopeDeclBlock (blk : Block) : Bool :=
  let t := blk.text.trimAscii
  t.startsWith "namespace" || t.startsWith "section" || t.startsWith "end" ||
  t.startsWith "variable"  || t.startsWith "variables" ||
  t.startsWith "parameter" || t.startsWith "parameters"

def isAmbientBlock (blk : Block) : Bool :=
  let t := blk.text.trimAscii
  t.startsWith "import"    || t.startsWith "prelude"  || t.startsWith "module" ||
  t.startsWith "/-!"       || t.startsWith "--"       ||
  t.startsWith "namespace" || t.startsWith "section"  || t.startsWith "end" ||
  t.startsWith "universe"  || t.startsWith "open"     || t.startsWith "attribute" ||
  t.startsWith "set_option"|| t.startsWith "local"    || t.startsWith "scoped" ||
  t.startsWith "notation"  || t.startsWith "infix"    || t.startsWith "prefix" ||
  t.startsWith "postfix"   || t.startsWith "macro"    || t.startsWith "macro_rules" ||
  t.startsWith "syntax"    ||
  t.startsWith "variable"  || t.startsWith "variables"||
  t.startsWith "parameter" || t.startsWith "parameters"

def minimalBlocksWithContext (e : Export) (target : Name) : Array Nat :=
  Id.run do
    let base := minimalBlocksFor e target
    if base.isEmpty then return #[]
    let hi := base.foldl (fun m x => Nat.max m x) 0
    let mut set : Std.HashSet Nat := {}
    for i in base do set := set.insert i
    for i in [: (hi + 1)] do
      if isAmbientBlock e.blocks[i]! then set := set.insert i
    pure (set.toArray.qsort (· < ·))

def renderIndices (e : Export) (indices : Array Nat) : String :=
  Id.run do
    let mut b : Array String := #[]

    unless e.header.trimAscii.isEmpty do
      b := b.push e.header
      if !e.header.endsWith "\n" then
        b := b.push "\n"

    let openFrame (f : ScopeFrame) : String :=
      match f.kind with
      | .namespace => "namespace " ++ f.name.toString ++ "\n"
      | .section =>
          if f.name == Name.anonymous then "section\n"
          else "section " ++ f.name.toString ++ "\n"

    let closeFrame (f : ScopeFrame) : String :=
      if f.name == Name.anonymous then "end\n"
      else "end " ++ f.name.toString ++ "\n"

    let mut currentScope : Array ScopeFrame := #[]

    for idx in indices do
      let some blk := e.blocks[idx]? | continue
      let targetScope := blk.scopes
      let mut common := 0
      while common < currentScope.size && common < targetScope.size && currentScope[common]! == targetScope[common]! do
        common := common + 1

      for i in [0:currentScope.size - common] do
        let sIdx := currentScope.size - 1 - i
        b := b.push (closeFrame currentScope[sIdx]!)
      for i in [common:targetScope.size] do
        b := b.push (openFrame targetScope[i]!)
      currentScope := targetScope
      if !isScopeDeclBlock blk then
        b := b.push blk.text
        if !blk.text.endsWith "\n" then b := b.push "\n"

    for i in [0:currentScope.size] do
      let sIdx := currentScope.size - 1 - i
      b := b.push (closeFrame currentScope[sIdx]!)
    String.intercalate "" b.toList

def sliceToString (e : Export) (target : Name) : String :=
  let indices := minimalBlocksWithContext e target
  renderIndices e indices

def emitQuiver (e : Export) : String := Id.run do
  let mut semanticBlocks : Array Nat := #[]
  let mut semanticOf : Std.HashMap Nat Nat := {}
  for i in [:e.blocks.size] do
    let blk := e.blocks[i]!
    if !blk.primaryProduces.isEmpty then
      let semanticIdx := semanticBlocks.size
      semanticBlocks := semanticBlocks.push i
      semanticOf := semanticOf.insert i semanticIdx
  let n := semanticBlocks.size
  let mut b : Array String := #[]

  b := b.push "import Mathlib.CategoryTheory.FreeCategory\n"
  b := b.push "import Mathlib.Algebra.Category.ModuleCat.Basic\n"
  b := b.push "import Mathlib.Data.Real.Basic\n"
  b := b.push "import Socratic\n\n"
  b := b.push "set_option maxRecDepth 2000000\n"

  b := b.push "namespace Socratic.Generated\n\n"
  b := b.push "inductive Obj\n"
  for i in [:n] do
    b := b.push s!"  | block_{i}\n"
  b := b.push "\ninductive Edge : Obj → Obj → Type\n"
  for origU in semanticBlocks do
    let some u := semanticOf.get? origU | continue
    for (origV, _) in e.blockGraph.forward[origU]! do
      let some v := semanticOf.get? origV | continue
      b := b.push s!"  | edge_{u}_{v} : Edge .block_{u} .block_{v}\n"

  b := b.push "\nnoncomputable def fileSyntax : Socratic.Syntax := {\n"
  b := b.push "  Obj := Obj,\n"
  b := b.push "  Hom := Edge\n"
  b := b.push "}\n\n"

  b := b.push "noncomputable def coreSem : Socratic.Semantics fileSyntax (Type) :=\n"
  b := b.push "  { obj := fun _ => PUnit,\n"
  b := b.push "    map := fun _ => id }\n\n"

  b := b.push "noncomputable def fileHomTriple : Socratic.HomTriple fileSyntax := {\n"
  b := b.push "  ProgSem := coreSem,\n"
  b := b.push "  SpecSem := coreSem,\n"
  b := b.push "  VecSem := coreSem,\n"
  b := b.push "  spec_isProp := by intro _; infer_instance,\n"
  b := b.push "  sound := 𝟙 _,\n"
  b := b.push "  encode := 𝟙 _\n"
  b := b.push "}\n\n"

  b := b.push "end Socratic.Generated\n"
  String.intercalate "" b.toList

def escapeLeanString (s : String) : String :=
  let s1 := s.replace "\\" "\\\\"
  let s2 := s1.replace "\n" "\\n"
  let s3 := s2.replace "\"" "\\\""
  s3

abbrev TacticStateData := Array String × Std.HashMap String Nat × Array (Nat × Nat × String × Nat)

def emitTacticQuiver (e : Export) : String := Id.run do
  let initData : TacticStateData := (#[], {}, #[])
  let (_, (states, _, edges)) := StateT.run (m := Id) (do
    let addState := fun (s : String) => do
      let (sts, map, edgs) ← get
      match map.get? s with
      | some idx => pure idx
      | none =>
        let idx := sts.size
        set (sts.push s, map.insert s idx, edgs)
        pure idx

    -- Add the terminal "done" state explicitly
    let _ ← addState "no goals"

    for blk in e.blocks do
      for morph in blk.morphisms do
        let stateBefore := if morph.beforeState.isEmpty then "no goals" else String.intercalate " | " morph.beforeState.toList
        let stateAfter := if morph.afterState.isEmpty then "no goals" else String.intercalate " | " morph.afterState.toList
        let u ← addState stateBefore
        let v ← addState stateAfter
        let (sts, map, edgs) ← get
        let eIdx := edgs.size
        set (sts, map, edgs.push (u, v, morph.tacticSyntax, eIdx))

  ) initData

  let mut b : Array String := #[]
  b := b.push "import Mathlib.CategoryTheory.FreeCategory\n"
  b := b.push "namespace TacticQuiver.Generated\n\n"

  b := b.push "inductive TacticStateObj\n"
  for i in [:states.size] do
    b := b.push s!"  | state_{i} -- {escapeLeanString states[i]!}\n"

  b := b.push "\ninductive TacticEdge : TacticStateObj → TacticStateObj → Type\n"
  for (u, v, tactic, i) in edges do
    b := b.push s!"  | edge_{i} : TacticEdge .state_{u} .state_{v} -- {escapeLeanString tactic}\n"

  b := b.push "\nend TacticQuiver.Generated\n"
  String.intercalate "" b.toList

end DAG

open DAG

/-- CLI entrypoint. -/
def blockExportMain (args : List String) : IO UInt32 := do
  match args with
  | ["--emit-tactic-quiver", outFileStr, fileStr] =>
    let ex ← exportFile (System.FilePath.mk fileStr)
    let quiverCode := emitTacticQuiver ex
    IO.FS.writeFile (System.FilePath.mk outFileStr) quiverCode
    return 0
  | ["--emit-quiver", outFileStr, fileStr] =>
    let ex ← exportFile (System.FilePath.mk fileStr)
    let quiverCode := emitQuiver ex
    IO.FS.writeFile (System.FilePath.mk outFileStr) quiverCode
    return 0
  | ["--slice", targetStr, fileStr] =>
    let target := targetStr.toName
    let ex ← exportFile (System.FilePath.mk fileStr)
    let sliced := sliceToString ex target
    IO.println sliced
    return 0
  | [fileStr] =>
    let ex ← exportFile (System.FilePath.mk fileStr)
    IO.println (toJson ex).pretty
    return 0
  | _ =>
    IO.eprintln "usage: block_export <lean-file>"
    IO.eprintln "       block_export --slice <Target.Name> <lean-file>"
    IO.eprintln "       block_export --emit-quiver <out.lean> <lean-file>"
    IO.eprintln "       block_export --emit-tactic-quiver <out.lean> <lean-file>"
    return 1
