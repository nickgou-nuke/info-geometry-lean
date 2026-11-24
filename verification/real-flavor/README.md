# Real flavor verification

This focused package checks three canonical real-matrix owners and their
repository imports at the root project's unchanged Lean and Mathlib pins:

- `InfoGeometry.Canonical.FlavorReadout`
- `InfoGeometry.Canonical.FlavorDiracGram`
- `InfoGeometry.Canonical.FlavorCompression`

From the repository root, with the pinned runtime on `PATH`:

```bash
python3 verification/real-flavor/check.py exe cache get
python3 verification/real-flavor/check.py --final
```

The final command holds the repository's exclusive shared build lock through
the targeted Lake build, fresh warning-as-error elaboration of every owner,
and the native owned-declaration audit. The audit uses
`tools.quality.reviewed_audit_source`: it traverses Lean's imported environment,
including generated and private declarations owned by the three modules, and
accepts only `propext`, `Classical.choice`, and `Quot.sound`. It rejects unsafe
or partial declarations and requires a reconciled nonzero count per owner.

Input snapshots include the transitive repository source closure, root and
focused configurations, verifier controls, and dependency configurations.
Pinned clean dependency commits and the actual Lean/Lake runtime are checked
before and after execution. A final passing receipt is written only after
those stability checks succeed. Logs, generated audit source, and receipts
live in a unique directory under `artifacts/verification/real-flavor`.

An existing directory of exact pinned dependency checkouts can be reused
without symlinking `.lake` or changing dependency revisions:

```bash
python3 verification/real-flavor/check.py \
  --dependency-root /absolute/path/to/existing/.lake/packages \
  --lake /absolute/path/to/pinned/runtime/bin/lake --final
```

The explicit directory is checked for its package inventory, revisions,
tracked cleanliness, and source/configuration shadowing. Lake's native
package-location option changes locations only; generated artifacts remain
writable under the same shared lock. `--no-wait` fails if that lock is occupied.

For a narrow development command, omit `--final` and pass ordinary Lake
arguments after `--`. Such an invocation is not the final acceptance sequence.

The focused result does not certify the root package, all repository files,
external projects, a physical interpretation, or an octonion specialization.
The root staged and publication gates remain separate checks. Mathematical
scope and remaining obligations are recorded in
[`REAL_FLAVOR_READOUT_CONTRACT.md`](../../docs/REAL_FLAVOR_READOUT_CONTRACT.md).
