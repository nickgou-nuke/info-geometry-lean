import Mathlib

 theorem foo_test_env_probe : True := by
  trivial

open Lean in
#eval do
  let env <- getEnv
  env.constants.toList.forM (fun (entry : Name × ConstantInfo) => do
    let n := entry.fst
    if (toString n).contains "foo_test_env_probe" then
      IO.println s!"FOUND:{n}")
