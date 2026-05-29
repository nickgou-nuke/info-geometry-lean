import Lean
import Lean.Data.Json
import DAG.Basic

open Lean

namespace DAG.ExprArangoExport

structure NodeRow where
  _key : String
  graphKind : String
  decl : String
  kind : String
  module : String
  sectionTag : String
  path : String
  exprTag : String
  info : String
  doc : String
  deBruijnIdx? : Option Nat := none
  deBruijnHash : String := ""
  alphaLocalHash : String := ""
  shapeHash : Nat := 0
  quality : String := "ok"
deriving Repr, ToJson

structure EdgeRow where
  _key : String
  _from : String
  _to : String
  kind : String
  role : String
  decl : String
  sectionTag : String
  deBruijnIdx? : Option Nat := none
  incidenceHash : String := ""
  binderIncidenceHash : String := ""
  quality : String := "ok"
  notes : String := ""
deriving Repr, ToJson

structure ExportMeta where
  schemaVersion : Nat
  importModules : String
  namespacePrefix : String
  selectedDecls : Nat
  nodes : Nat
  edges : Nat
  brokenBVarCount : Nat
  includeExternalDecls : Bool
  includeGeneratedDecls : Bool
  maxDecls : Nat
deriving Repr, ToJson

structure ExportState where
  nodes : Array NodeRow := #[]
  edges : Array EdgeRow := #[]
  declKeyMap : Std.HashMap Name String := {}
  nextExprNodeId : Nat := 0
  nextEdgeId : Nat := 0
  brokenBVarCount : Nat := 0
deriving Inhabited

abbrev ExportM := StateT ExportState IO

private def schemaVersion : Nat := 1

private def dottedName (s : String) : Name :=
  (s.splitOn ".").foldl (init := Name.anonymous) fun acc part =>
    if part.isEmpty then acc else Name.str acc part

private def parseImports (s : String) : Array Import :=
  let mods := (s.splitOn ",").filter (fun x => x != "")
  mods.foldl (init := #[]) fun acc m => acc.push { module := dottedName m }

private def normalizePrefix? (s : String) : Option String :=
  if s = "" || s = "*" then none else some s

private def inNamespace (nsPrefix? : Option String) (n : Name) : Bool :=
  match nsPrefix? with
  | none => true
  | some p =>
      let s := toString n
      s = p || s.startsWith (p ++ ".")

private def generatedLike (n : Name) : Bool :=
  let s := toString n
  s.contains "._" || s.endsWith "match_" || s.endsWith "proof_" || s.endsWith "injEq"

private def kindString : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .quotInfo _ => "quot"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

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

private def getDocString (env : Environment) (n : Name) : IO String := do
  match ← Lean.findDocString? env n with
  | some d => pure d
  | none => pure ""

private def declKeyOf (n : Name) : String :=
  s!"d_{(hash (toString n)).toNat}"

private def shapeHashOf (e : Expr) : Nat :=
  (hash (toString e)).toNat

private def stableHashString (s : String) : String :=
  s!"h_{(hash s).toNat}"

private def deBruijnNodeHash (decl sectionTag path : String) (idx : Nat) : String :=
  stableHashString s!"debruijn-node|{decl}|{sectionTag}|{path}|{idx}"

private def deBruijnIncidenceHash
    (decl sectionTag sourceKey targetKey : String)
    (idx : Nat) : String :=
  stableHashString s!"debruijn-incidence|{decl}|{sectionTag}|{sourceKey}|{targetKey}|{idx}"

private def binderAt? (binders : Array String) (idx : Nat) : Option String :=
  if idx < binders.size then
    let revIdx := binders.size - 1 - idx
    some (binders[revIdx]!)
  else
    none

private def exprTagOf : Expr → String
  | .bvar _ => "bvar"
  | .fvar _ => "fvar"
  | .mvar _ => "mvar"
  | .sort _ => "sort"
  | .const _ _ => "const"
  | .app _ _ => "app"
  | .lam _ _ _ _ => "lam"
  | .forallE _ _ _ _ => "forallE"
  | .letE _ _ _ _ _ => "letE"
  | .lit (.natVal _) => "lit_nat"
  | .lit (.strVal _) => "lit_str"
  | .mdata _ _ => "mdata"
  | .proj _ _ _ => "proj"

private def exprInfoOf : Expr → String
  | .bvar idx => s!"{idx}"
  | .fvar id => toString id.name
  | .mvar id => toString id.name
  | .sort lvl => toString lvl
  | .const name _ => toString name
  | .lit (.natVal v) => s!"{v}"
  | .lit (.strVal s) => s
  | .proj s i _ => s!"{s}.{i}"
  | _ => ""

private def freshExprNodeKey : ExportM String := do
  let st ← get
  let key := s!"x_{st.nextExprNodeId}"
  set { st with nextExprNodeId := st.nextExprNodeId + 1 }
  pure key

private def freshEdgeKey : ExportM String := do
  let st ← get
  let key := s!"e_{st.nextEdgeId}"
  set { st with nextEdgeId := st.nextEdgeId + 1 }
  pure key

private def addNode (row : NodeRow) : ExportM Unit :=
  modify fun st => { st with nodes := st.nodes.push row }

private def addEdge
    (fromKey toKey kind role decl sectionTag : String)
    (deBruijnIdx? : Option Nat := none)
    (incidenceHash : String := "")
    (quality : String := "ok")
    (notes : String := "") : ExportM Unit := do
  let ek ← freshEdgeKey
  let row : EdgeRow := {
    _key := ek
    _from := s!"ig_nodes/{fromKey}"
    _to := s!"ig_nodes/{toKey}"
    kind := kind
    role := role
    decl := decl
    sectionTag := sectionTag
    deBruijnIdx? := deBruijnIdx?
    incidenceHash := incidenceHash
    quality := quality
    notes := notes
  }
  modify fun st => { st with edges := st.edges.push row }

private def bumpBrokenBVar : ExportM Unit :=
  modify fun st => { st with brokenBVarCount := st.brokenBVarCount + 1 }

private def ensureDeclNode (env : Environment) (name : Name) : ExportM String := do
  let st ← get
  match st.declKeyMap.get? name with
  | some key => pure key
  | none =>
      let key := declKeyOf name
      let moduleName := moduleNameFor env name
      let kind :=
        match env.find? name with
        | some ci => kindString ci
        | none => "unknown"
      let doc ← getDocString env name
      let row : NodeRow := {
        _key := key
        graphKind := "decl"
        decl := toString name
        kind := kind
        module := moduleName
        sectionTag := ""
        path := ""
        exprTag := ""
        info := ""
        doc := doc
        shapeHash := (hash (toString name)).toNat
        quality := if env.find? name |>.isSome then "ok" else "broken"
      }
      modify fun s =>
        { s with
          nodes := s.nodes.push row
          declKeyMap := s.declKeyMap.insert name key
        }
      pure key

def visitExpr
    (env : Environment)
    (declName : Name)
    (sectionTag : String)
    (path : String)
    (binders : Array String)
    (includeExternalDecls : Bool)
    (e : Expr) : ExportM String := do
  let key ← freshExprNodeKey
  let base : NodeRow := {
    _key := key
    graphKind := "expr"
    decl := toString declName
    kind := "expr"
    module := moduleNameFor env declName
    sectionTag := sectionTag
    path := path
    exprTag := exprTagOf e
    info := exprInfoOf e
    doc := ""
    shapeHash := shapeHashOf e
    quality := "ok"
  }
  match e with
  | .bvar idx =>
      let isBroken := (binderAt? binders idx).isNone
      let row := {
        base with
        deBruijnIdx? := some idx
        deBruijnHash := deBruijnNodeHash (toString declName) sectionTag path idx
        quality := if isBroken then "broken" else "ok"
      }
      addNode row
      match binderAt? binders idx with
      | some binderKey =>
          addEdge key binderKey "bind" "bound_by" (toString declName) sectionTag
            (some idx)
            (deBruijnIncidenceHash (toString declName) sectionTag key binderKey idx)
      | none =>
          bumpBrokenBVar
      pure key
  | .fvar _ =>
      addNode base
      pure key
  | .mvar _ =>
      addNode base
      pure key
  | .sort _ =>
      addNode base
      pure key
  | .const cname _ =>
      addNode base
      if includeExternalDecls then
        let target ← ensureDeclNode env cname
        addEdge key target "const_ref" "const_ref" (toString declName) sectionTag
      pure key
  | .app fn arg =>
      addNode base
      let fnKey ← visitExpr env declName sectionTag (path ++ ".fn") binders includeExternalDecls fn
      let argKey ← visitExpr env declName sectionTag (path ++ ".arg") binders includeExternalDecls arg
      addEdge key fnKey "ast" "fn" (toString declName) sectionTag
      addEdge key argKey "ast" "arg" (toString declName) sectionTag
      pure key
  | .lam _ ty body _ =>
      addNode base
      let tyKey ← visitExpr env declName sectionTag (path ++ ".type") binders includeExternalDecls ty
      addEdge key tyKey "ast" "type" (toString declName) sectionTag
      let bodyKey ← visitExpr env declName sectionTag (path ++ ".body") (binders.push key) includeExternalDecls body
      addEdge key bodyKey "ast" "body" (toString declName) sectionTag
      pure key
  | .forallE _ ty body _ =>
      addNode base
      let tyKey ← visitExpr env declName sectionTag (path ++ ".type") binders includeExternalDecls ty
      addEdge key tyKey "ast" "type" (toString declName) sectionTag
      let bodyKey ← visitExpr env declName sectionTag (path ++ ".body") (binders.push key) includeExternalDecls body
      addEdge key bodyKey "ast" "body" (toString declName) sectionTag
      pure key
  | .letE _ ty val body _ =>
      addNode base
      let tyKey ← visitExpr env declName sectionTag (path ++ ".type") binders includeExternalDecls ty
      let valKey ← visitExpr env declName sectionTag (path ++ ".value") binders includeExternalDecls val
      addEdge key tyKey "ast" "type" (toString declName) sectionTag
      addEdge key valKey "ast" "value" (toString declName) sectionTag
      let bodyKey ← visitExpr env declName sectionTag (path ++ ".body") (binders.push key) includeExternalDecls body
      addEdge key bodyKey "ast" "body" (toString declName) sectionTag
      pure key
  | .lit _ =>
      addNode base
      pure key
  | .mdata _ body =>
      addNode base
      let bodyKey ← visitExpr env declName sectionTag (path ++ ".expr") binders includeExternalDecls body
      addEdge key bodyKey "ast" "expr" (toString declName) sectionTag
      pure key
  | .proj _ _ body =>
      addNode base
      let bodyKey ← visitExpr env declName sectionTag (path ++ ".expr") binders includeExternalDecls body
      addEdge key bodyKey "ast" "expr" (toString declName) sectionTag
      pure key

private def createDirAllFrom (path : System.FilePath) : IO Unit :=
  match path.parent with
  | some p => IO.FS.createDirAll p
  | none => pure ()

private def writeJsonl {α} [ToJson α] (path : System.FilePath) (rows : Array α) : IO Unit := do
  createDirAllFrom path
  let lines := String.intercalate "\n" <| rows.toList.map (fun row => (toJson row).compress)
  IO.FS.writeFile path (if lines.isEmpty then "" else lines ++ "\n")

private def writeMetadata (path : System.FilePath) (metadata : ExportMeta) : IO Unit := do
  createDirAllFrom path
  IO.FS.writeFile path (toJson metadata).pretty

private def parseNatDefault (s : String) (default : Nat) : Nat :=
  match s.toNat? with
  | some n => n
  | none => default

private def parseBoolDefault (s : String) (default : Bool) : Bool :=
  let lower := s.toLower
  if lower = "true" || lower = "1" || lower = "yes" then true
  else if lower = "false" || lower = "0" || lower = "no" then false
  else default

private def collectDeclTargets
    (env : Environment)
    (nsPrefix? : Option String)
    (maxDecls : Nat)
    (includeGeneratedDecls : Bool) : Array Name :=
  let names :=
    env.constants.toList.foldl (init := #[]) fun acc (name, ci) =>
      if !inNamespace nsPrefix? name then
        acc
      else if !includeGeneratedDecls && generatedLike name then
        acc
      else
        match ci with
        | .thmInfo _ | .axiomInfo _ | .defnInfo _ | .opaqueInfo _ | .inductInfo _ =>
            acc.push name
        | _ =>
            acc
  let sorted := names.qsort (fun a b => toString a < toString b)
  if maxDecls == 0 then sorted else sorted.extract 0 (Nat.min maxDecls sorted.size)

private def runExport
    (importModsStr nsPrefix outDirStr : String)
    (maxDecls : Nat)
    (includeExternalDecls : Bool)
    (includeGeneratedDecls : Bool) : IO UInt32 := do
  let imports := parseImports importModsStr
  let env ← importModules imports {} 0
  let nsPrefix? := normalizePrefix? nsPrefix
  let targets := collectDeclTargets env nsPrefix? maxDecls includeGeneratedDecls

  IO.println s!"[ExprArangoExport] imported modules={importModsStr}"
  IO.println s!"[ExprArangoExport] selected declarations={targets.size}"

  let mut st : ExportState := {}

  for name in targets do
    let (declKey, st1) ← (ensureDeclNode env name).run st
    st := st1
    match env.find? name with
    | none => pure ()
    | some ci =>
        let (typeRoot, st2) ←
          (visitExpr env name "type" "type" #[] includeExternalDecls ci.type).run st
        st := st2
        let (_, st3) ← (addEdge declKey typeRoot "decl_root" "type_root" (toString name) "type").run st
        st := st3
        match ci.value? with
        | none => pure ()
        | some val =>
            let (valRoot, st4) ←
              (visitExpr env name "value" "value" #[] includeExternalDecls val).run st
            st := st4
            let (_, st5) ← (addEdge declKey valRoot "decl_root" "value_root" (toString name) "value").run st
            st := st5

  let outDir := System.FilePath.mk outDirStr
  writeJsonl (outDir / "ig_nodes.jsonl") st.nodes
  writeJsonl (outDir / "ig_edges.jsonl") st.edges
  writeMetadata (outDir / "metadata.json") {
    schemaVersion := schemaVersion
    importModules := importModsStr
    namespacePrefix := nsPrefix
    selectedDecls := targets.size
    nodes := st.nodes.size
    edges := st.edges.size
    brokenBVarCount := st.brokenBVarCount
    includeExternalDecls := includeExternalDecls
    includeGeneratedDecls := includeGeneratedDecls
    maxDecls := maxDecls
  }
  IO.println s!"[ExprArangoExport] wrote {outDirStr}/ig_nodes.jsonl"
  IO.println s!"[ExprArangoExport] wrote {outDirStr}/ig_edges.jsonl"
  IO.println s!"[ExprArangoExport] broken bvar records={st.brokenBVarCount}"
  pure 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [importModsStr, nsPrefix, outDir] =>
      runExport importModsStr nsPrefix outDir 0 true true
  | [importModsStr, nsPrefix, outDir, maxDeclsStr] =>
      runExport importModsStr nsPrefix outDir (parseNatDefault maxDeclsStr 0) true true
  | [importModsStr, nsPrefix, outDir, maxDeclsStr, includeExternalStr] =>
      runExport importModsStr nsPrefix outDir
        (parseNatDefault maxDeclsStr 0)
        (parseBoolDefault includeExternalStr true)
        true
  | [importModsStr, nsPrefix, outDir, maxDeclsStr, includeExternalStr, includeGeneratedStr] =>
      runExport importModsStr nsPrefix outDir
        (parseNatDefault maxDeclsStr 0)
        (parseBoolDefault includeExternalStr true)
        (parseBoolDefault includeGeneratedStr true)
  | _ =>
      IO.eprintln "usage: ExprArangoExport <import-module[,module2,...]> <namespace-prefix|*> <output-dir> [max-decls] [include-external-decls] [include-generated-decls]"
      IO.eprintln "example:"
      IO.eprintln "  lake env lean --run lean/DAG/ExprArangoExport.lean InfoGeometry.Audit InfoGeometry artifacts/expr-graph/raw-lossless 0 true true"
      pure 1

end DAG.ExprArangoExport

def main (args : List String) : IO UInt32 :=
  DAG.ExprArangoExport.main args
