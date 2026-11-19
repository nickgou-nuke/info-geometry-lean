/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Lean
open Lean

def collectAxiomsIn (env : Environment) (name : Name) : IO (Array Name) := do
  let ctx : Core.Context := {
    fileName := "axiom_index"
    fileMap := FileMap.ofString ""
  }
  (Lean.collectAxioms name : CoreM (Array Name)).toIO' ctx { env := env }

def emitModuleDecls (env : Environment) (label : String) (mod : ModuleData) : IO Unit := do
  IO.println s!"MODULE:{label}"
  let ctx : Core.Context := {
    fileName := "axiom_index"
    fileMap := FileMap.ofString ""
  }
  let act : CoreM Unit := do
    -- Iterate module's own declarations in one CoreM pass
    for (name, ci) in mod.constNames.zip mod.constants do
      let k : String :=
        match ci with
        | .thmInfo _ => "theorem"
        | .defnInfo _ => "def"
        | .opaqueInfo _ => "opaque"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
        | .axiomInfo _ => "axiom"
        | _ => "other"
      if k ∉ ["theorem", "def", "opaque", "inductive", "axiom"] then continue
      let isPart := ci.isPartial && !name.toString.endsWith "_unsafe_rec"
      let isUnsafe := ci.isUnsafe
      let isAxiom := k == "axiom"
      let axioms ← Lean.collectAxioms name
      IO.println s!"DECL:{name}:kind={k}:partial={isPart}:unsafe={isUnsafe}:axiom={isAxiom}:axioms={axioms}"
  act.toIO' ctx { env := env }

def showAxioms (path : System.FilePath) : IO Unit := do
  let (mod, _) ← readModuleData path
  let env ← importModules mod.imports {} 0
  -- Replay module constants into environment
  let mut newC : Std.HashMap Name ConstantInfo := {}
  for (name, ci) in mod.constNames.zip mod.constants do
    newC := newC.insert name ci
  let kernelEnv ← env.toKernelEnv.replay newC
  let env := Environment.ofKernelEnv kernelEnv
  emitModuleDecls env path.toString mod

def parseModuleSpec (raw : String) : Except String (Name × System.FilePath) := do
  match raw.splitOn "=" with
  | modStr :: rest =>
    let pathStr := "=".intercalate rest
    if modStr.isEmpty || pathStr.isEmpty then
      throw s!"invalid module spec '{raw}'"
    let modName := (modStr.splitOn ".").foldl Name.str Name.anonymous
    return (modName, ⟨pathStr⟩)
  | [] => throw s!"invalid module spec '{raw}'"

def showAxiomsFastBatch (specs : List (Name × System.FilePath)) : IO Unit := do
  let mut loaded : Array (System.FilePath × ModuleData) := #[]
  for (_, path) in specs do
    let (mod, _) ← readModuleData path
    loaded := loaded.push (path, mod)
  let imports := specs.toArray.map fun (m, _) => { module := m }
  let env ← importModules imports {} 1024
  for (path, mod) in loaded do
    emitModuleDecls env path.toString mod

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "Usage: lake env lean --run tools/infra/axiom_index.lean [--fast-modules Mod=Path... | --replay file.olean... | file.olean...]"
    return 1
  initSearchPath (← findSysroot)
  match args with
  | "--fast-modules" :: rest =>
    if rest.isEmpty then
      IO.eprintln "No module specs provided for --fast-modules"
      return 1
    let mut specs : List (Name × System.FilePath) := []
    for item in rest do
      match parseModuleSpec item with
      | .ok spec => specs := specs ++ [spec]
      | .error err =>
        IO.eprintln err
        return 1
    showAxiomsFastBatch specs
    return 0
  | "--replay" :: rest =>
    if rest.isEmpty then
      IO.eprintln "No .olean paths provided for --replay"
      return 1
    for arg in rest do
      showAxioms ⟨arg⟩
    return 0
  | _ =>
    for arg in args do
      showAxioms ⟨arg⟩
    return 0
