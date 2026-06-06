import Lean

open Lean

def ALLOWED : Array Name :=
  #[`propext, `Quot.sound, `Classical.choice]

def checkOne (path : System.FilePath) : IO Bool := do
  IO.eprintln s!"Checking {path}"
  let (mod, _) ← readModuleData path
  let env ← importModules mod.imports {} 0
  let mut allClean := true

  for name in mod.constNames do
    unless env.contains name do
      continue
    match env.find? name with
    | none => continue
    | some ci =>
      -- Check partial
      if ci.isPartial && !name.toString.endsWith "_unsafe_rec" then
        IO.eprintln s!"  {name}: PARTIAL"
        allClean := false
      -- Check unsafe
      if ci.isUnsafe then
        IO.eprintln s!"  {name}: UNSAFE"
        allClean := false
      -- Collect axioms
      let axioms : Array Name := Lean.collectAxioms name
      let disallowed := axioms.filter fun a => !(ALLOWED.contains a)
      if !disallowed.isEmpty then
        IO.eprintln s!"  {name}: disallowed axioms {disallowed}"
        allClean := false

  if allClean then
    IO.eprintln s!"  ✓ all {mod.constNames.size} declarations clean"
  return allClean

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "Usage: lake env lean --run tools/infra/axiom_check.lean <file1.olean> [file2.olean ...]"
    return 1
  let mut anyFailed := false
  for arg in args do
    let ok ← checkOne ⟨arg⟩
    if !ok then anyFailed := true
  if anyFailed then
    IO.eprintln "\n❌ Some modules have violations."
    return 1
  else
    IO.eprintln "\n✓ All modules passed."
    return 0
