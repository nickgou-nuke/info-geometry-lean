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

syntax "#dumpGraphDot" str : command

elab_rules : command
  | `(#dumpGraphDot $path:str) => do
      let env ← getEnv
      let g := DAG.envToGraph env

      let mut lines : Array String := #["digraph InfoGeometryEnv {"]
      for (src, dst) in g.edges do
        lines := lines.push s!"  \"{src}\" -> \"{dst}\";"
      lines := lines.push "}"

      let outPath := path.getString
      liftIO <| IO.FS.writeFile outPath (String.intercalate "\n" lines.toList)
      logInfo m!"wrote DOT graph to {outPath}"

#dumpGraph
-- #dumpGraphDot "/tmp/env.dot"
