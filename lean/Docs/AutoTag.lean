import Lean
import InfoGeometry
import DAG.Basic
import DAG.Hydrate
import DAG.Analysis

open Lean
open DAG

/-- Print `[blueprint]` annotations only for the structural Core Skeleton
of the Information Geometry theory.  The namespace is passed as a command‑line
argument. Example:

```bash
lake env lean --run lean/Docs/AutoTag.lean InfoGeometry > lean/Docs/all_blueprints.lean
```
-/
def main (args : List String) : IO UInt32 := do
  let ns := args.headD ""
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `InfoGeometry }] {}
  let g := buildGraphFromEnv env (some ns)
  let h := hydrate g

  -- Extract True Skeleton with a threshold (e.g., minimum 1 vulnerability dependency)
  let skel := extractTheorySkeleton h 1
  for (name, _, _) in skel do
    let s := name.toString
    if ns == "" || s.startsWith (ns ++ ".") then
      if !name.isAnonymous then
        IO.println s!"@[blueprint] {name}"

  return 0
