import Lean
import Lean.Data.Json
import DAG.Basic

open Lean

namespace DAG.GlobalDisassembler

structure GraphNode where
  id : Nat
  kind : String
  info : Json
  deriving ToJson

structure GraphEdge where
  source : Nat
  target : Nat
  role : String
  deriving ToJson

structure DeclarationNode where
  id : Nat
  name : String
  module : String
  deriving ToJson
abbrev GraphM := StateT (Std.HashMap Expr Nat × Nat × Nat) IO

def nextNodeId : GraphM Nat := do
  let (map, nodeCount, declCount) ← get
  set (map, nodeCount + 1, declCount)
  return nodeCount

def nextDeclId : GraphM Nat := do
  let (map, nodeCount, declCount) ← get
  set (map, nodeCount, declCount + 1)
  return declCount

def writeNode (h : IO.FS.Handle) (kind : String) (info : Json) : GraphM Nat := do
  let id ← nextNodeId
  let node := { id := id, kind := kind, info := info : GraphNode }
  h.putStrLn (toJson node).compress
  return id

def writeEdge (h : IO.FS.Handle) (source target : Nat) (role : String) : GraphM Unit := do
  let edge := { source := source, target := target, role := role : GraphEdge }
  h.putStrLn (toJson edge).compress

def writeDecl (h : IO.FS.Handle) (name : String) (module : String) : GraphM Nat := do
  let id ← nextDeclId
  let decl := { id := id, name := name, module := module : DeclarationNode }
  h.putStrLn (toJson decl).compress
  return id

partial def visitExprGlobal (hNodes hEdges : IO.FS.Handle) (e : Expr) : GraphM Nat := do
  let (map, _, _) ← get
  if let some id := map.get? e then
    return id

  let id ← match e with
    | .bvar idx => writeNode hNodes "bvar" (toJson idx)
    | .fvar id => writeNode hNodes "fvar" (toJson (toString id.name))
    | .mvar id => writeNode hNodes "mvar" (toJson (toString id.name))
    | .sort lvl => writeNode hNodes "sort" (toJson (toString lvl))
    | .const name _ => writeNode hNodes "const" (toJson (toString name))
    | .app fn arg => do
        let id ← writeNode hNodes "app" Json.null
        let fnId ← visitExprGlobal hNodes hEdges fn
        let argId ← visitExprGlobal hNodes hEdges arg
        writeEdge hEdges id fnId "fn"
        writeEdge hEdges id argId "arg"
        pure id
    | .lam _ t b _ => do
        let id ← writeNode hNodes "lam" Json.null
        let tId ← visitExprGlobal hNodes hEdges t
        let bId ← visitExprGlobal hNodes hEdges b
        writeEdge hEdges id tId "type"
        writeEdge hEdges id bId "body"
        pure id
    | .forallE _ t b _ => do
        let id ← writeNode hNodes "forallE" Json.null
        let tId ← visitExprGlobal hNodes hEdges t
        let bId ← visitExprGlobal hNodes hEdges b
        writeEdge hEdges id tId "type"
        writeEdge hEdges id bId "body"
        pure id
    | .letE _ t v b _ => do
        let id ← writeNode hNodes "letE" Json.null
        let tId ← visitExprGlobal hNodes hEdges t
        let vId ← visitExprGlobal hNodes hEdges v
        let bId ← visitExprGlobal hNodes hEdges b
        writeEdge hEdges id tId "type"
        writeEdge hEdges id vId "value"
        writeEdge hEdges id bId "body"
        pure id
    | .lit (.natVal v) => writeNode hNodes "lit_nat" (toJson v)
    | .lit (.strVal v) => writeNode hNodes "lit_str" (toJson v)
    | .mdata _ e => do
        let id ← writeNode hNodes "mdata" Json.null
        let eId ← visitExprGlobal hNodes hEdges e
        writeEdge hEdges id eId "expr"
        pure id
    | .proj s i e => do
        let id ← writeNode hNodes "proj" (toJson (toString s ++ "." ++ toString i))
        let eId ← visitExprGlobal hNodes hEdges e
        writeEdge hEdges id eId "expr"
        pure id

  modify fun (map, nc, dc) => (map.insert e id, nc, dc)
  return id

def processEnvironment (env : Environment) (outNodes outEdges outDecls outDeclEdges : String) : IO Unit := do
  let hNodes ← IO.FS.Handle.mk outNodes IO.FS.Mode.write
  let hEdges ← IO.FS.Handle.mk outEdges IO.FS.Mode.write
  let hDecls ← IO.FS.Handle.mk outDecls IO.FS.Mode.write
  let hDeclEdges ← IO.FS.Handle.mk outDeclEdges IO.FS.Mode.write

  let mut state : Std.HashMap Expr Nat × Nat × Nat := ({}, 0, 0)

  for (name, ci) in env.constants do
    if !(toString name).startsWith "Nat" then continue

    let (declId, newState) ← (writeDecl hDecls (toString name) "unknown_module").run state
    state := newState

    let (typeId, newState2) ← (visitExprGlobal hNodes hEdges ci.type).run state
    state := newState2

    hDeclEdges.putStrLn (toJson ({ source := declId, target := typeId, role := "HAS_TYPE" } : GraphEdge)).compress

    if let some val := ci.value? then
      let (valId, newState3) ← (visitExprGlobal hNodes hEdges val).run state
      state := newState3
      hDeclEdges.putStrLn (toJson ({ source := declId, target := valId, role := "HAS_VALUE" } : GraphEdge)).compress

  IO.println s!"Export complete. Nodes: {state.2.1}, Declarations: {state.2.2}"

end DAG.GlobalDisassembler

def globalDisassemblerMain (_args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Init : Import }] {}
  DAG.GlobalDisassembler.processEnvironment env "nodes.jsonl" "edges.jsonl" "decls.jsonl" "decl_edges.jsonl"
  return 0
