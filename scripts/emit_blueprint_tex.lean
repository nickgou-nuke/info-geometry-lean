import Lean
import InfoGeometry.Analysis
open Lean


def jsonEscape (s : String) : String :=
  "\"" ++ s.toList.foldl (fun acc c =>
    match c with
    | '\"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | _ => acc ++ String.singleton c) "" ++ "\""

-- reuse the dependency collector from the analysis package
abbrev analysisCollectDeps := InfoGeometry.Analysis.collectDeps

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

def main : IO UInt32 := do
  -- `IO.getArgs` is not available; use `Lean.getArgs` which returns `List String`.
  let args ← Lean.Syntax.getArgs
  match args with
  | [proj, ns, out] =>
    let env ← importModules proj {} >>= fun _ => getEnv
    let decls := env.constants.toList.filter (fun (n, _) => n.toString.startsWith ns)
    writeDecls (System.FilePath.mk out) decls
    return 0
  | _ =>
    IO.eprintln "usage: ExportDecls <project> <namespace> <out>"
    return 1