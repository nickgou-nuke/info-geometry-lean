import Lean
open Lean

def collectAxiomsIn (env : Environment) (name : Name) : IO (Array Name) := do
  let ctx : Core.Context := {
    fileName := "axiom_index"
    fileMap := FileMap.ofString ""
  }
  (Lean.collectAxioms name : CoreM (Array Name)).toIO' ctx { env := env }

def showAxioms (path : System.FilePath) : IO Unit := do
  let (mod, _) ← readModuleData path
  let env ← importModules mod.imports {} 0
  -- Replay module constants into environment
  let mut newC : Std.HashMap Name ConstantInfo := {}
  for (name, ci) in mod.constNames.zip mod.constants do
    newC := newC.insert name ci
  let kernelEnv ← env.toKernelEnv.replay newC
  let env := Environment.ofKernelEnv kernelEnv
  -- Iterate module's own declarations
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
    -- Collect axioms via the replayed environment
    let axioms ← collectAxiomsIn env name
    IO.println s!"DECL:{name}:kind={k}:partial={isPart}:unsafe={isUnsafe}:axiom={isAxiom}:axioms={axioms}"

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "Usage: lake env lean --run tools/infra/axiom_index.lean <file.olean>..."
    return 1
  for arg in args do
    showAxioms ⟨arg⟩
  return 0
