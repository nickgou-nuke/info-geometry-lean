import Lean
import InfoGeometry.All

open Lean

partial def exprToAst (e : Expr) : Json :=
  match e with
  | .bvar idx => Json.mkObj [("type", "bvar"), ("idx", idx)]
  | .fvar fv => Json.mkObj [("type", "fvar"), ("name", fv.name.toString)]
  | .mvar mv => Json.mkObj [("type", "mvar"), ("name", mv.name.toString)]
  | .sort l => Json.mkObj [("type", "sort"), ("level", toString l)]
  | .const n _ => Json.mkObj [("type", "const"), ("name", n.toString)]
  | .app f a => Json.mkObj [("type", "app"), ("f", exprToAst f), ("a", exprToAst a)]
  | .lam n t b _ => Json.mkObj [("type", "lam"), ("var", n.toString), ("type_ast", exprToAst t), ("body", exprToAst b)]
  | .forallE n t b _ => Json.mkObj [("type", "forallE"), ("var", n.toString), ("type_ast", exprToAst t), ("body", exprToAst b)]
  | .letE n t v b _ => Json.mkObj [("type", "letE"), ("var", n.toString), ("type_ast", exprToAst t), ("val", exprToAst v), ("body", exprToAst b)]
  | .lit l =>
    let litStr := match l with
      | .natVal v => toString v
      | .strVal s => s
    Json.mkObj [("type", "lit"), ("val", litStr)]
  | .mdata _ e => exprToAst e
  | .proj s i e => Json.mkObj [("type", "proj"), ("s", s.toString), ("idx", i), ("expr", exprToAst e)]

def constInfoToJson (c : ConstantInfo) : Json :=
  let name := c.name.toString
  let typeAst := exprToAst c.type
  let valAst := match c.value? with
    | some v => exprToAst v
    | none => Json.null
  Json.mkObj [
    ("name", name),
    ("type_ast", typeAst),
    ("value_ast", valAst)
  ]

def main : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `InfoGeometry.All }] {}
  let mut decls : Array Json := #[]
  for (n, c) in env.constants do
    if (`InfoGeometry).isPrefixOf n then
      decls := decls.push (constInfoToJson c)
  let out : Json := Json.arr decls
  IO.FS.writeFile "graph.json" out.pretty
