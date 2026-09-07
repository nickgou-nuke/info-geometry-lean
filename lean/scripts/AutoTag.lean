import Lean
import InfoGeometry   -- ensure project module is loaded
open Lean

/-- Print `[blueprint]` annotations for every constant under the
optional namespace prefix.  The namespace is passed as a command‑line
argument.  Example:

```bash
lake env lean --run lean/AutoTag.lean InfoGeometry > lean/all_blueprints.lean
```

If no prefix is given, all constants are listed. -/
def main (args : List String) : IO UInt32 := do
  let ns := args.headD ""
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `InfoGeometry }] {}
  for (name, _) in env.constants do
    let s := name.toString
    if ns == "" || s.startsWith (ns ++ ".") then
      if !name.isAnonymous then
        IO.println s!"@[blueprint] {name}"
  return 0

def runMain : List String → IO UInt32 := main
