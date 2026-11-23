/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Lean

/-!
# Polarized Z/2-Graded Framework E2E Axiom Audit Helper

Standalone `--run` Lean 4 script and canonical reference snippet for auditing
E2E tier files and imported `InfoGeometry.*` owner modules.

## Standalone Usage
```bash
python3 tools/infra/run_locked_lean.py --wait-for-build-lock --run \
  tests/polarized_z2_e2e/AxiomAuditHelper.lean \
  InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
```
Each argument may be either a dotted module name (resolved under
`.lake/build/lib/lean/`) or an explicit `.olean` file path.

## Canonical Inline `E2EAxiomAudit` Snippet for `Tier*_*.lean`
Because `lakefile.lean` is frozen and `tests/polarized_z2_e2e/*.lean` files
cannot import each other under `run_locked_lean.py`, each `Tier*_*.lean` file
imports `Lean.Util.CollectAxioms` and `Lean.Elab.Command` and embeds the
following self-checking block at the bottom of the file:

```lean
section E2EAxiomAudit
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut audited : Nat := 0
  for (name, info) in env.constants do
    if (env.getModuleIdxFor? name).isSome then continue
    if name.toString.startsWith "_private." then continue
    match info with
    | .thmInfo _ | .defnInfo _ =>
      if info.isUnsafe || info.isPartial then
        throwError "Unsafe or partial E2E declaration: {name}"
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Disallowed axiom {ax} in E2E declaration {name}"
      audited := audited + 1
    | .axiomInfo _ =>
      throwError "Disallowed axiom declaration in E2E file: {name}"
    | _ => pure ()
  if audited == 0 then
    throwError "E2EAxiomAudit found 0 declarations in current module"
  logInfo m!"E2E_AXIOM_AUDIT_PASS: {audited} local declarations verified"
end E2EAxiomAudit
```
-/

open Lean

namespace PolarizedZ2E2E.AxiomAuditHelper

/-- Permitted foundational Lean 4 axioms. -/
def allowedAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

/-- Resolve either a `.olean` path or a dotted module name under `.lake/build/lib/lean/`. -/
def resolveOleanPath (target : String) : System.FilePath :=
  if target.endsWith ".olean" || target.contains '/' || target.contains '\\' then
    ⟨target⟩
  else
    let relPath := "/".intercalate (target.splitOn ".") ++ ".olean"
    ⟨".lake/build/lib/lean/" ++ relPath⟩

/-- Collect all transitive axioms for `declName` in `env`. -/
def collectAxiomsIn (env : Environment) (declName : Name) : IO (Array Name) := do
  let ctx : Core.Context := {
    fileName := "AxiomAuditHelper"
    fileMap := FileMap.ofString ""
  }
  (Lean.collectAxioms declName : CoreM (Array Name)).toIO' ctx { env := env }

/-- Replay and audit a single `.olean` target (module or path). -/
def checkTarget (target : String) : IO Bool := do
  let path := resolveOleanPath target
  if !(← path.pathExists) then
    IO.eprintln s!"Checking {target} -> {path}: MISSING_OLEAN"
    IO.println s!"MODULE_RESULT:{target}:FAIL"
    return false
  IO.eprintln s!"Checking {target} ({path})"
  let (mod, _) ← readModuleData path
  let env ← importModules mod.imports {} 0
  let mut newConstants : Std.HashMap Name ConstantInfo := {}
  for (name, ci) in mod.constNames.zip mod.constants do
    newConstants := newConstants.insert name ci
  let kernelEnv ← env.toKernelEnv.replay newConstants
  let replayedEnv := Environment.ofKernelEnv kernelEnv
  let mut allClean := true

  for (name, ci) in mod.constNames.zip mod.constants do
    if ci.isPartial && !name.toString.endsWith "_unsafe_rec" then
      IO.eprintln s!"  {name}: PARTIAL"
      allClean := false
    if ci.isUnsafe then
      IO.eprintln s!"  {name}: UNSAFE"
      allClean := false
    match ci with
    | .axiomInfo _ =>
      IO.eprintln s!"  {name}: AXIOM_DECLARATION"
      allClean := false
    | _ => pure ()
    let axioms ← collectAxiomsIn replayedEnv name
    let disallowed := axioms.filter fun ax => !(allowedAxioms.contains ax)
    if !disallowed.isEmpty then
      IO.eprintln s!"  {name}: disallowed axioms {disallowed}"
      allClean := false

  if allClean then
    IO.eprintln s!"  ok: all {mod.constNames.size} declarations clean"
  let verdict := if allClean then "PASS" else "FAIL"
  IO.println s!"MODULE_RESULT:{target}:{verdict}"
  return allClean

end PolarizedZ2E2E.AxiomAuditHelper

/-- CLI entry point for `lean --run tests/polarized_z2_e2e/AxiomAuditHelper.lean <ModuleOrOlean...>`. -/
def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "Usage: run_locked_lean.py --run tests/polarized_z2_e2e/AxiomAuditHelper.lean <ModuleOrOlean...>"
    return 1
  Lean.initSearchPath (← Lean.findSysroot)
  let mut anyFailed := false
  for target in args do
    let ok ← PolarizedZ2E2E.AxiomAuditHelper.checkTarget target
    if !ok then
      anyFailed := true
  if anyFailed then
    IO.eprintln "AxiomAuditHelper: FAIL"
    return 1
  IO.eprintln "AxiomAuditHelper: PASS"
  return 0
