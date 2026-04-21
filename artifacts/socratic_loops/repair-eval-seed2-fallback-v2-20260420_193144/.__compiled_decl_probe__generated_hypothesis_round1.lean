import Lean
open Lean in
#eval do
  let env <- importModules #[{ module := `generated_hypothesis_round1 }] {}
  let some targetIdx := env.getModuleIdx? `generated_hypothesis_round1 |
    IO.println "ERROR:NO_MODULE_IDX:generated_hypothesis_round1"
    return
  for (entry : Name × ConstantInfo) in env.constants.toList do
    let declName := entry.fst
    if env.getModuleIdxFor? declName == some targetIdx then
      IO.println s!"DECL:{declName}"
