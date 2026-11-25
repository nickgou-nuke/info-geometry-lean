# Quadratic, Lorentz incidence, and operator symmetry validation

The theorem meanings, intake provenance, existing-owner reuse, and open scope
are recorded in `docs/PARA_TWISTOR_NOETHER_CONTRACT.md`.

## Reproduce the native transaction

With the repository-pinned Lean 4.34.1 runtime on `PATH`, run from the repository
root:

```bash
python3 -B verification/para-twistor-noether/check.py
```

The runner reuses the unchanged `verification/real-matrix-split` package. It
holds the maintained shared build lock across pin checks, source snapshots,
runtime checks, explicit builds, fresh warnings-as-errors source elaboration,
and native declaration/axiom auditing. The final snapshot and package checks
must match their initial values. The receipt is
`artifacts/para-twistor-noether/native/result.json`; each invocation has its own
log directory and replaces the receipt with `queued` before waiting.

The five selected modules are:

- `InfoGeometry.OperatorAlgebra.OperatorDirichlet.MatrixLegendreResidual`
- `InfoGeometry.Twistor.RealLorentzTwistorIncidence`
- `InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceTriple`
- `InfoGeometry.Clifford.AnticommutatorSymmetry`
- `InfoGeometry.Canonical.ParaTwistorNoetherChecks`

Native ownership is determined by Lean's environment, including generated and
private declarations. The runner reconciles module counts, declaration rows,
and every explicitly named public declaration. It also audits the selected
critical reused declarations. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted foundational axioms.

## Reusing an exact pinned local cache

When the nine dependencies already exist in another ordinary checkout, the
runner accepts Lake's supported package-location override:

```bash
python3 -B verification/para-twistor-noether/check.py \
  --packages /absolute/path/exact-pin-packages.json
```

That file is a partial Lake manifest with `"version": "1.2.0"` and a
`"packages"` array containing exactly the nine names in the unchanged focused
manifest. Preserve each entry's `name`, `scope`, `inherited`, `configFile`, and
`manifestFile`; use `"type": "path"` and an absolute `dir` for its existing
checkout. No root/focused manifest or toolchain file is rewritten.

The runner checks focused pins against the root, requires the fixed Mathlib
revision `d13f23b723b8a846827a245b89c10fc7d3f11612`, and checks each actual
dependency HEAD and tracked cleanliness before and after. It rejects linked
worktrees or symlinked Lake roots using the existing workspace guard. Normal
builds may update generated artifacts in the shared cache under the lock.

## Independent acceptance and publication

The native runner does not certify semantic interpretation or the entire root
package. Independent semantic review and the unchanged staged/push gates are
separate acceptance steps. Source scans are also separate from kernel checks.

The source consumers exercise a positive quadratic form with off-diagonal
entries, coincident/null/timelike graph cases, noncommuting matrix units, a
nonzero corner triple, actual unit-conjugation and commutator intertwiners, and
a nonzero trace-rate counterexample without the commutation hypothesis.

Current execution status belongs in the run receipt and the PR validation
record. The existence of this runner is not evidence that a native pass or
publication gate has occurred.
