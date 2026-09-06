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
#eval do
  -- `IO.getArgs` is not defined; `Lean.getArgs` supplies command-line args
  let ns := (← Lean.getArgs).headD ""
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    let s := name.toString
    when (ns == "" || s.startsWith (ns ++ ".")) do
      unless name.isAnonymous do
        match ci with
        | .thmInfo _ | .axiomInfo _ | .defnInfo _ | .opaqueInfo _
        | .inductInfo _ | .ctorInfo _ | .quotInfo _ | .recInfo _ =>
            IO.println s!"@[blueprint] {name}"
        | _ => pure ()
