# Lean Build Coverage Policy

The active Lean verification surface is the set of roots in
`proofs/lakefile.toml` plus modules imported by those roots.  A successful

```bash
cd proofs
lake build -R
```

means that this active surface type-checks.

Historical/prototype files that were formerly listed as roots but no longer
represent current theorem-honest certificates have been moved to:

```text
proofs/_deprecated/removed_from_default_2026_06_15/
```

Those files are deliberately outside the active library.  They may contain stale
imports, `sorry`, axioms, or prototype/vacuous declarations and must not be cited
as checked certificates until repaired and re-added to `lakefile.toml`.

Promotion rule:

1. Move the file back under `proofs/`.
2. Repair it so it compiles in the current mathlib environment.
3. Avoid `sorry`/unjustified axioms for algebraic kernels.
4. Add it to `proofs/lakefile.toml`.
5. Run `cd proofs && lake build -R`.
