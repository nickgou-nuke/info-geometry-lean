import Lean
open Lean in
#eval do
  let env <- importModules #[{ module := `TmpExtract }] {}
  let some targetIdx := env.getModuleIdx? `TmpExtract |
    IO.println "ERROR:NO_MODULE_IDX:TmpExtract"
    return
  for (entry : Name × ConstantInfo) in env.constants.toList do
    let declName := entry.fst
    if env.getModuleIdxFor? declName == some targetIdx then
      IO.println s!"DECL:{declName}"
