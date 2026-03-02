import Lean
import DAG.Basic
open Lean


def jsonEscape (s : String) : String :=
  "\"" ++ s.toList.foldl (fun acc c =>
    match c with
    | '\"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | _ => acc ++ String.singleton c) "" ++ "\""

-- reuse the dependency collector from the analysis package
def analysisCollectDeps (e : Expr) : List Name := (DAG.collectExprConsts e).toList

def getDeps (ci : Lean.ConstantInfo) : List String :=
  match ci.value? with
  | some val => (analysisCollectDeps val).map (fun n => n.toString)
  | none => []

def writeDecls (out : System.FilePath) (decls : List (Lean.Name × Lean.ConstantInfo)) : IO Unit := do
  let lines := decls.map fun (n, c) =>
    let mod := n.getPrefix.toString
    let deps := getDeps c
    let depsJson := "[" ++ String.intercalate "," (deps.map jsonEscape) ++ "]"
    "  { \"name\": " ++ jsonEscape n.toString ++
      ", \"module\": " ++ jsonEscape mod ++
      ", \"deps\": " ++ depsJson ++ " }"
  let body := "[\n" ++ String.intercalate ",\n" lines ++ "\n]"
  IO.FS.writeFile out body

@[export main]
def emitBlueprintTexMain (args : List String) : IO UInt32 := do
  match args with
  | proj :: ns :: outPath :: _ =>
    initSearchPath (← findSysroot)
    let env ← importModules #[{ module := proj.toName }] {}
    let decls := env.constants.toList.filter (fun (n, _) => (n.toString).startsWith ns)
    writeDecls (System.FilePath.mk outPath) decls
    return 0
  | _ =>
    IO.eprintln "usage: emit_blueprint_tex <project> <namespace> <output>"
    return 1
