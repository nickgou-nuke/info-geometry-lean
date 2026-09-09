import Lean
import Lean.Parser.Module
import Lean.Elab.Frontend

open Lean
open Lean.Parser
open Lean.Elab

/-- Data for a single Atomic Declaration. -/
structure Atom where
  name : String
  kind : String
  source : String
  deps : List String
deriving ToJson, Repr

/-- Extract dependencies for a constant. -/
def getDeps (env : Environment) (n : Name) : List String :=
  match env.find? n with
  | none => []
  | some ci => 
    let deps := ci.type.foldConsts (init := NameSet.empty) (fun n s => s.insert n)
    let deps := match ci.value? with
      | some v => v.foldConsts (init := deps) (fun n s => s.insert n)
      | none => deps
    deps.toList.map (fun n => n.toString)

/-- Heuristic to find Name in syntax -/
partial def findName (s : Syntax) : Option Name :=
  let k := s.getKind
  if k == `Lean.Parser.Command.defId then
    some s[0].getId
  else if k == `Lean.Parser.Command.theoremId then
    some s[0].getId
  else
    match s with
    | .node _ _ args => args.findSome? findName
    | _ => none

def atomizeFile (env : Environment) (fileName : String) : IO (List Atom) := do
  let input ← IO.FS.readFile fileName
  let inputCtx := mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  
  let mut atoms : List Atom := []
  let mut curState := parserState
  let mut curMessages := messages
  let parserContext : Parser.ParserModuleContext := {
    env := env,
    options := {}
  }
  
  while true do
    let (stx, nextState, nextMessages) := Parser.parseCommand inputCtx parserContext curState curMessages
    curState := nextState
    curMessages := nextMessages
    
    let kind := stx.getKind
    if kind == ``Lean.Parser.Command.declaration then
      match stx.getPos?, stx.getTailPos? with
      | some pos, some tailPos =>
        let source := input.extract pos tailPos
        
        if let some declName := findName stx then
          atoms := { 
            name := declName.toString, 
            kind := kind.toString, 
            source := source, 
            deps := getDeps env declName
          } :: atoms
      | _, _ => pure ()

    if stx.isToken "eoi" then break

  return atoms.reverse

def main (args : List String) : IO UInt32 := do
  let (importMod, filePath) ← match args with
    | [m, f] => pure (m, f)
    | _ => 
      IO.eprintln "Usage: Atomizer <import-module> <file-to-atomize>"
      return 1
  
  let env ← importModules #[{ module := importMod.toName }] {} 0
  let atoms ← atomizeFile env filePath
  
  let json := ToJson.toJson atoms
  IO.println json.pretty
  return 0
