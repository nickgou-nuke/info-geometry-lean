# Focused Castro CT audit checks

This driver checks the four canonical owners named in `check.py` through the
existing `verification/real-matrix-split` package. It does not add a Lake
package or change any dependency pin.

From the repository root, with the pinned Lean toolchain on `PATH`:

```bash
python3 verification/castro-ct/check.py
```

To perform only the source phase:

```bash
python3 verification/castro-ct/check.py --source-only
```

Each run writes its logs and `verification.json` under
`artifacts/verification/castro-ct`, or a distinct `--output-dir`. These are
generated run artifacts and are not committed. The source-only status is
explicitly `source_checks_passed_kernel_pending`.

The full command inventories public declarations, checks forbidden proof
constructs and dependency pins, runs static/semantic checks, then submits one
serial compiler batch through the maintained shared-lock wrapper. The batch
builds all four owners, freshly elaborates each with warnings as errors, and
runs the generated declaration axiom audit. Only `propext`, `Classical.choice`,
and `Quot.sound` are permitted by that audit.

Source hashes are checked for changes during each phase. A full success
requires both a successful wrapper exit and the complete expected compiler
receipt. Waiting for the lock is not compilation. Static review is not a
kernel check. The result covers the named owners and their imports in this
focused package, not the root package, mirrored `src/` sources, or the entire
repository.

See the [theorem contract](../../handover/injections/castro-ct-spectral-audit-20261123.md)
for mathematical scope, corrections to the supplied proposal, and remaining
analytic obligations.
