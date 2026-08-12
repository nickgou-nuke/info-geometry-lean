import Lean
import Mathlib.Tactic
import InfoGeometry.External.Auto.ExtractBraid

open Lean
open Lean.Meta
open Lean.Elab.Command

/-- 
  A simple Lean 4 Metaprogramming tool to extract AST nodes and dependency edges 
  from the environment and dump them as JSON for ArangoDB ingestion.
-/

structure ASTNode where
  name : String
  type : String
  kind : String
  deriving ToJson

structure ASTEdge where
  from_node : String
  to_node   : String
  relation  : String
  deriving ToJson

structure ASTGraphData where
  nodes : Array ASTNode
  edges : Array ASTEdge
  deriving ToJson

/-- Collect all constant names using an executable explicit worklist. -/
def collectConstants (e : Expr) (acc : NameSet := {}) : NameSet := Id.run do
  let mut pending : Array Expr := #[e]
  let mut names := acc
  while h : pending.size > 0 do
    let current := pending.back!
    pending := pending.pop
    match current with
    | Expr.const n _ => names := names.insert n
    | Expr.app f a => pending := pending.push f |>.push a
    | Expr.lam _ d b _ => pending := pending.push d |>.push b
    | Expr.forallE _ d b _ => pending := pending.push d |>.push b
    | Expr.letE _ t v b _ => pending := pending.push t |>.push v |>.push b
    | Expr.mdata _ body => pending := pending.push body
    | Expr.proj _ _ struct => pending := pending.push struct
    | _ => pure ()
  return names

/-- Command to extract the dependency graph of a specific module prefix -/
elab "#extract_graph " prefixName:ident : command => do
  let env ← getEnv
  let prefixStr := prefixName.getId.toString
  
  let mut nodes : Array ASTNode := #[]
  let mut edges : Array ASTEdge := #[]
  
  for (name, cinfo) in env.constants.toList do
    let nameStr := name.toString
    -- Only index our specific modules to avoid dumping the entirety of Mathlib
    if nameStr.startsWith prefixStr &&
        !(nameStr.startsWith "Lean" || nameStr.startsWith "Mathlib" || nameStr.startsWith "Init" || nameStr.startsWith "Std" || nameStr.startsWith "Aesop" || nameStr.startsWith "Qq" || nameStr.startsWith "Cli" || nameStr.startsWith "Lake") then
      let kind := match cinfo with
        | ConstantInfo.thmInfo _ => "Theorem"
        | ConstantInfo.defnInfo _ => "Definition"
        | ConstantInfo.axiomInfo _ => "Axiom"
        | ConstantInfo.inductInfo _ => "Inductive"
        | ConstantInfo.ctorInfo _ => "Constructor"
        | _ => "Other"

      nodes := nodes.push { name := nameStr, type := toString cinfo.type, kind := kind }
      
      -- Extract edges by looking at the body of definitions and theorems
      let valOpt := cinfo.value?
      if let some val := valOpt then
        let deps := collectConstants val
        for dep in deps do
          let depStr := dep.toString
          -- Create an edge if it depends on something (we can filter for our modules or keep all)
          edges := edges.push { from_node := nameStr, to_node := depStr, relation := "depends_on" }

  let graph : ASTGraphData := { nodes := nodes, edges := edges }
  let jsonStr := toJson graph |>.pretty
  
  -- We output to a file that our Python pipeline can pick up
  let path : System.FilePath := ⟨"ast_graph.json"⟩
  IO.FS.writeFile path jsonStr
  logInfo s!"Graph extracted! Nodes: {nodes.size}, Edges: {edges.size}. Saved to ast_graph.json"
