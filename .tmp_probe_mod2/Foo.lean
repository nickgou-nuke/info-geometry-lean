import Lean
open Lean Elab Command

theorem foo_test_env_probe : True := by
  trivial

elab "#dumpCurrentModuleDecls" : command => do
  let env <- getEnv
  let main := env.header.mainModule
  logInfo m!"MAIN:{main}"
  logInfo m!"MODULES:{env.header.moduleNames}"
  logInfo m!"IDX? theorem = {env.getModuleIdxFor? `foo_test_env_probe}"

#dumpCurrentModuleDecls
