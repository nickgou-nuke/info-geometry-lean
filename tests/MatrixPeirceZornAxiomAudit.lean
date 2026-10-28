/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixPeirceZorn
import Lean.Util.CollectAxioms

/-! Transitive axiom audit of every declaration in this development. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut theoremCount : Nat := 0
  let names := env.constants.fold (init := #[]) fun acc name info =>
    if name.toString.startsWith "InfoGeometry.Canonical.MatrixPeirceZorn." ||
        name.toString.startsWith "_private.InfoGeometry.Canonical.MatrixPeirceZorn." then
      acc.push (name, info)
    else acc
  for (name, info) in names.qsort (fun a b => Name.quickLt a.1 b.1) do
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Unapproved axiom dependency: {name}: {axiomName}"
    count := count + 1
    match info with
    | .thmInfo _ => theoremCount := theoremCount + 1
    | _ => pure ()
    logInfo m!"{name}: {axioms}"
  if count == 0 then
    throwError "MatrixPeirceZorn audit selected no declarations"
  logInfo m!"PASS: {count} declarations, {theoremCount} theorem constants; only standard Lean axioms."
