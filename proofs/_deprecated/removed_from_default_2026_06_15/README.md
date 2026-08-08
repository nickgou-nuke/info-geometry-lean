# Removed from default proof target on 2026-06-15

These Lean files are historical/prototype certificates that were previously listed as
roots in `proofs/lakefile.toml` but are not part of the current theorem-honest
build surface.

They were moved here instead of being silently omitted from the default target.
This quarantine makes build semantics explicit:

- `lake build -R` checks the active proof library roots in `lakefile.toml`.
- Files in this directory are deprecated/prototype material and are not claimed
  as current checked certificates.
- To promote a file back into the active library, first repair it so it compiles
  without `sorry`/unjustified axioms, then move it back to `proofs/` and add it
  to `lakefile.toml`.
