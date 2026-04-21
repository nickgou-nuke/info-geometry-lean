import Lean
open Lean Elab Command

theorem foo_test_env_probe : True := by
  trivial

elab "#dumpCurrentModuleDecls" : command => do
  let env <- getEnv
  let main := env.header.mainModule
  let some mainIdx := env.getModuleIdx? main |
    logInfo m!"NO_MAIN_IDX:{main}"
  let mut names : List Name := []
  for (declName, _) in env.constants.toList do
    if env.getModuleIdxFor? declName == some mainIdx then
      names := declName :: names
  logInfo m!"DECLS:{names.reverse}"

#dumpCurrentModuleDecls
