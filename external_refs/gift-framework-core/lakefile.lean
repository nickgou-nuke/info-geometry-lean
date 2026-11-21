import Lake
open Lake DSL

package «GIFT»

@[default_target]
lean_lib «GIFT» where
  globs := #[.submodules `GIFT]
