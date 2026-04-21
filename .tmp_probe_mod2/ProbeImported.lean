import Lean
open Lean in
#eval do
  let env <- importModules #[{module := `Foo}] {}
  IO.println s!"MAIN:{env.header.mainModule}"
  IO.println s!"IDX:{env.getModuleIdx? `Foo}"
  IO.println s!"DECLIDX:{env.getModuleIdxFor? `foo_test_env_probe}"
