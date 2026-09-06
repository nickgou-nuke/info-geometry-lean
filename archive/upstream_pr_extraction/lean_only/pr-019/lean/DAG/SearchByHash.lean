import Lean
import DAG.ExprFingerprint

open Lean

namespace DAG.SearchByHash

structure HashMatch where
  name : Name
  kind : String
  role : String -- "type" or "value"
deriving ToJson, Repr

private def getKindString (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _    => "theorem"
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "def"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .quotInfo _   => "quotient"
  | .ctorInfo _   => "constructor"
  | .recInfo _    => "recursor"

def searchAndPrintByHash (targetHash : UInt64) : MetaM Unit := do
  let env ← getEnv
  let mut found := false
  for (name, ci) in env.constants do
    let typeHash := DAG.computeShapeHash ci.type
    if typeHash == targetHash then
      IO.println s!"{getKindString ci} {name} (type)"
      found := true
    
    if let some val := ci.value? then
      let valHash := DAG.computeShapeHash val
      if valHash == targetHash then
        IO.println s!"{getKindString ci} {name} (value)"
        found := true
  if !found then
    IO.println "No matches found."

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: SearchByHash <hash> [import1,module2,...]"
    return 1
  
  let targetHash? := args[0]!.toNat?.map (·.toUInt64)
  if targetHash?.isNone then
    IO.eprintln s!"invalid hash: {args[0]!}"
    return 1
  let targetHash := targetHash?.get!

  let imports := 
    if args.length > 1 then
      args[1]!.splitOn "," |>.filter (· != "") |>.map fun m => 
        { module := (m.splitOn ".").foldl (init := Name.anonymous) fun acc part => Name.str acc part }
    else
      #[{ module := `InfoGeometry.All }]

  initSearchPath (← findSysroot)
  let env ← importModules imports.toArray {} 0
  
  let coreContext : Lean.Core.Context := { 
    options := {}, 
    currNamespace := Name.anonymous, 
    openDecls := [], 
    fileName := "<SearchByHash>", 
    fileMap := default, 
    maxHeartbeats := 0, 
    maxRecDepth := 1000 
  }
  let act : CoreM (Unit × Meta.State) := (searchAndPrintByHash targetHash).run {} {}
  let _ ← act.toIO coreContext { env := env }
  return 0

end DAG.SearchByHash

def main (args : List String) : IO UInt32 :=
  DAG.SearchByHash.main args
