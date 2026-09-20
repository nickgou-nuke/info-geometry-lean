# Default Lean source coverage

The default Lake libraries include the active `InfoGeometry`, `Omega`, `DAG`,
`Agent`, `Docs`, `Socratic`, `SelfReference`, `Experimental`, `VirasoroProject`,
`scripts`, audit, standalone-mathematics, and test sources. This is build
selection, not a claim that all those modules currently compile.

`InfoGeometry.All` imports `InfoGeometry.AllExhaustive`. Default-selected
modules are included there unless they depend on that umbrella themselves.
In particular, `InfoGeometry.auto_blueprints` and `InfoGeometry.BlueprintTags`
must remain downstream to avoid an import cycle; both are default-built.

Run `python3 tools/infra/audit_default_lean_sources.py` for a read-only check
of default selection, source existence, Git tracking, and umbrella coverage.
The strict-check pipeline runs this audit before its builds. A newly selected
module missing from the umbrella, or a source missing from the Git index,
causes the check to fail. This does not stage files automatically.

Use the shared-lock wrapper for verification:

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock
```

`lake build -R` re-elaborates Lake configuration; `-R` is not an all-files
selection flag. Do not run another compiler while the shared build is active.

## Remaining integration boundaries

- `PrimitiveSetsAboveX` is an explicitly opt-in external proof requiring a
  different Lean toolchain. Its pins are unchanged.
- Root probes, nested Lake configuration files, generated annotation copies,
  caches, recovery trees, and archives are not promoted as active libraries.
- Twenty misplaced mathematical modules were moved from root `InfoGeometry/`
  into `lean/InfoGeometry/`, without changing their contents.
- Five absolute, broken links under `lean/` now reference their tracked
  `proofs/` sources using repository-relative links.
- The broader `proofs/` integration is not complete. The initial byte-level
  audit found 1,061 files: 13 identical to an existing selected source and
  1,048 not identical. Non-identical does not mean a new theorem owner: for
  example, `proofs/WeakIsospinSU2.lean` and its active `External/Auto` owner
  declare the same namespace and theorem names with different imports.
  These require source reconciliation and kernel checks, not blanket imports.

The source audit covers configured default libraries, not this unresolved
proof archive. A passing source audit must not be reported as proof that
every `.lean` file anywhere in the repository has been integrated or compiled.
