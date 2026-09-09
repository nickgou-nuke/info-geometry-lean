import Lean
import DAG.Basic
open Std   -- bring String.isPrefixOf

open Lean Elab Command

elab "#dumpGraph" : command => do
  let env ← getEnv

  -- collect names via fold rather than converting to list
  let names : Array Name :=
    env.constants.fold (init := #[]) (fun acc name _ =>
      if name.toString.startsWith "DAG." then
        acc.push name
      else
        acc)

  let names := names.qsort (fun a b => a.toString < b.toString)

  for name in names do
    match env.find? name with
    | none => pure ()
    | some ci =>
        logInfo m!"{name} : {ci.type}"

#dumpGraph
