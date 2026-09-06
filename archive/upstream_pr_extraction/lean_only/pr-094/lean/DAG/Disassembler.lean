import Lean
import Lean.Data.Json
import DAG.Basic

open Lean

namespace DAG

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

structure ExprGraph where
  nodes : Array GraphNode
  edges : Array GraphEdge
  deriving ToJson

abbrev GraphM := StateT (Std.HashMap Expr Nat × ExprGraph) Id

def addNode (kind : String) (info : Json) : GraphM Nat := do
  let (map, g) ← get
  let id := g.nodes.size
  let node := { id := id, kind := kind, info := info : GraphNode }
  set (map, { g with nodes := g.nodes.push node })
  return id

def addEdge (source target : Nat) (role : String) : GraphM Unit := do
  let (map, g) ← get
  let edge := { source := source, target := target, role := role : GraphEdge }
  set (map, { g with edges := g.edges.push edge })

def visitExpr (e : Expr) : GraphM Nat := do
  let (map, _) ← get
  if let some id := map.get? e then
    return id

  let id ← match e with
    | .bvar idx => addNode "bvar" (toJson idx)
    | .fvar id => addNode "fvar" (toJson (toString id.name))
    | .mvar id => addNode "mvar" (toJson (toString id.name))
    | .sort lvl => addNode "sort" (toJson (toString lvl))
    | .const name _ => addNode "const" (toJson (toString name))
    | .app fn arg => do
        let id ← addNode "app" Json.null
        let fnId ← visitExpr fn
        let argId ← visitExpr arg
        addEdge id fnId "fn"
        addEdge id argId "arg"
        pure id
    | .lam _ t b _ => do
        let id ← addNode "lam" Json.null -- omitting variable name for exact structural graph
        let tId ← visitExpr t
        let bId ← visitExpr b
        addEdge id tId "type"
        addEdge id bId "body"
        pure id
    | .forallE _ t b _ => do
        let id ← addNode "forallE" Json.null -- omitting variable name
        let tId ← visitExpr t
        let bId ← visitExpr b
        addEdge id tId "type"
        addEdge id bId "body"
        pure id
    | .letE _ t v b _ => do
        let id ← addNode "letE" Json.null
        let tId ← visitExpr t
        let vId ← visitExpr v
        let bId ← visitExpr b
        addEdge id tId "type"
        addEdge id vId "value"
        addEdge id bId "body"
        pure id
    | .lit (.natVal v) => addNode "lit_nat" (toJson v)
    | .lit (.strVal v) => addNode "lit_str" (toJson v)
    | .mdata _ e => do
        let id ← addNode "mdata" Json.null
        let eId ← visitExpr e
        addEdge id eId "expr"
        pure id
    | .proj s i e => do
        let id ← addNode "proj" (toJson (toString s ++ "." ++ toString i))
        let eId ← visitExpr e
        addEdge id eId "expr"
        pure id

  modify fun (map, g) => (map.insert e id, g)
  return id

def disassembleExpr (e : Expr) : ExprGraph :=
  let (_, (_, g)) := (visitExpr e).run ({}, { nodes := #[], edges := #[] })
  g

def disassembleConst (env : Environment) (name : Name) : Option ExprGraph :=
  match env.find? name with
  | some ci =>
      match ci.value? with
      | some val => some (disassembleExpr val)
      | none => none
  | none => none

end DAG
