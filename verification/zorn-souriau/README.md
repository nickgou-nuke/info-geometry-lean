# Focused Zorn/Souriau validation

The six source owners are listed in `check.py`. The driver uses the unchanged
`verification/real-matrix-split` package, whose `InfoGeometry` library resolves
the actual repository owners. It uses the root toolchain and exact Git pins;
it does not change the root manifest or substitute another mathematical model.

From the checkout root:

```bash
python3 -B verification/zorn-souriau/check.py
```

An existing set of ordinary dependency checkouts may be reused through Lake's
official package-location override:

```bash
python3 -B verification/zorn-souriau/check.py --packages /absolute/path/to/packages.json
```

Each override must name exactly one of the nine pinned packages, preserve its
scope/configuration/manifest fields, and give an absolute path to an ordinary,
clean Git checkout at the exact pinned revision. The driver verifies those
conditions before and after validation. Symlinked Lake roots, linked Git
worktrees, changed tracked dependency files, and changed pins are rejected.

The complete transaction holds the repository's shared build lock. It records
the exact source hashes, compiler versions, commands, and unique per-run logs;
builds the six targets; freshly elaborates each with warnings as errors; and
audits all declarations owned by the modules, including generated/private
declarations, plus seventeen critical reused declarations. Native declaration
inventories and per-owner row counts are reconciled. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted as foundational axioms.

Task sources and the frozen intake should be staged before the final run so
that the tracked-input snapshot includes them. Generated logs belong under
`artifacts/zorn-souriau/native`, not in source commits. The driver additionally
includes every target source and itself even before staging.

The runtime's `LEAN_NUM_THREADS` setting may be set to `1` in a constrained
environment; this changes resource concurrency, not proof statements or pins.
Run no other compiler/build command in parallel. Do not nest the driver inside
another holder of the same lock.

This is focused native acceptance, not a whole-repository build certificate
or a replacement for the publication hook. See `SOURCE_REVIEW.md` for the
actual observed status of this change.

The `Native Zorn and Souriau intake` GitHub workflow checks out the exact PR
head, uses the existing locked cache-hydration route, and runs this same driver.
It records the commit/tree and uploads the native receipt and complete logs.
Its presence does not imply a successful run. The inherited generic left-unit
criterion comes from PR #441; the six new owners add the right action,
Ell-circular consumers, and separate Souriau fragments. A parent PR's status
does not substitute for checking the imported declarations here.
