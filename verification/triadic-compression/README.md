# Focused verification of tripotent compression

This project checks the canonical sources in `../../lean`, with the exact
root Lean and Mathlib revisions. It shares ordinary dependency directories
inside this independent checkout; no Lake directory is symlinked. Its own
build products remain under this verification project's `.lake/build`.

After committing the implementation, run from the repository root with Lean
`v4.34.1` on `PATH`:

```bash
python3 verification/triadic-compression/audit.py
```

The driver first builds the audit target and then runs the Lean audit afresh.
Each subprocess uses `check.py`, the existing workspace-integrity check, and
the global build lock. Invoke the driver directly; do not wrap it in `check.py`.
The driver requires the selected sources and configurations to match the
committed bytes before and after verification, and checks dependency revisions.
Its JSON result and full command logs are written to the ignored `logs/`
directory. Use `--output PATH` to choose the JSON destination.

The audit enumerates all declarations owned by the selected nine modules,
checks transitive axiom dependencies against `propext`, `Classical.choice`,
and `Quot.sound`, and rejects newly introduced axioms or unsafe declarations.
It emits direct references from declaration types and proof/definition bodies
between the selected owner declarations. The driver checks complete inventory,
two expected proof dependencies, edge endpoints, and acyclicity, and records a
deterministic topological ordering. This is an inspectable dependency graph of
Lean declarations, not a newly formalized theorem about a `PartialOrder` object.

The focused build does not certify the root's unrelated path dependencies,
all default targets, or its publication gate. Root integration status and
independent acceptance are reported separately in `RESULTS.md`.

The exact mathematical scope and rejected implications are recorded in
[`TRIADIC_COMPRESSION_CONTRACT.md`](../../docs/TRIADIC_COMPRESSION_CONTRACT.md).
