# Default Lean source coverage

The canonical default Lake libraries include the active `InfoGeometry`, `Omega`, `DAG`,
`Agent`, `Docs`, `Socratic`, `SelfReference`, `Experimental`, `VirasoroProject`,
`scripts`, audit, standalone-mathematics, and test sources. This is build
selection, not a claim that all those modules currently compile. The separate
`lakefile.src.lean` workspace selects every Lean module under each source-bearing
top-level directory in `src/` and every top-level `.lean` file. It uses
`.lake/src-build` so shared module names have independent artifacts.
The root-level `src/PrimitiveSetsAboveX.lean` compatibility module is selected
in the source lane, matching the canonical Lake default target. Its metadata
records the upstream toolchain, while the local compatibility module is
retargeted to this repository's pinned toolchain.

`InfoGeometry.All` imports `InfoGeometry.AllExhaustive`. The intended contract
is that every default-selected `InfoGeometry.*` module is reachable from that
umbrella unless it depends on the umbrella itself. The current canonical audit
still reports unreachable default modules, so that contract is not yet closed.
`InfoGeometry.auto_blueprints` and `InfoGeometry.BlueprintTags` remain
downstream to avoid an import cycle; both are default-built.

Run `python3 tools/infra/audit_default_lean_sources.py` for a read-only check
of canonical default selection, source existence, Git tracking, and umbrella
coverage. The strict-check pipeline also runs the separate source-lane audit,
which validates `src/` selection against its explicit Lake globs. The locked
combined default-build mode is configured to compile both lanes; it still needs
a completed run before it can serve as build evidence. A newly selected canonical module
missing from the umbrella, or a source missing from the Git index, causes the
canonical audit to fail. This does not stage files automatically.

Use the shared-lock wrapper for verification:

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock --all-default-targets
```

`lake build -R` re-elaborates Lake configuration; `-R` is not an all-files
selection flag. Do not run another compiler while the shared build is active.

## Remaining integration boundaries

- `PrimitiveSetsAboveX` is a locally retargeted compatibility module for a
  pinned external proof. The upstream and local toolchains are recorded in
  `InfoGeometry.Arithmetic.Erdos1196ProofPin`.
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

The source audits cover configured source lanes, not archived or generated
trees. A passing audit must not be reported as proof that every `.lean` file
anywhere in the repository has been integrated or compiled.
