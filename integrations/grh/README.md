# Pinned GRH compatibility

This optional package connects the canonical InfoGeometry arithmetic and real
doubled readouts to the readable edition of
[`lsernau/grh-lean`](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh).
The canonical repository keeps its own Lean and Mathlib versions.

| Lane | Lean | Mathlib | External proof |
| --- | --- | --- | --- |
| `native` | 4.34.1 | `d13f23b723b8a846827a245b89c10fc7d3f11612` | None |
| `external` | 4.35.0 | `56a005855ea17e0b0958f73ec801ae140b0a1679` | GRH `72fead102f663d5c7a407964a13dc0cf9d977207`, subdirectory `grh` |

Both lanes compile the same files under `lean/`; no source copy or alternate
axiom is used to adapt the versions. The native lane needs only Mathlib and its
pinned dependencies, so unrelated optional root packages are outside its build
scope. The external lane also builds `New.Main` and its transitive proof imports.

## Mathematical consumers

`InfoGeometryGRH.VerifiedGRH` supplies the repository's existing Dirichlet
half-plane predicate from `New.grh` and derives Mathlib's `RiemannHypothesis`.

`InfoGeometryGRH.PrimeRemainderBridge` identifies the weighted native centered
smoothing divided by `x` with `New.primeRemainder`. It consumes the upstream
one-sided estimate to discharge the native weighted square-root growth
predicate. Its Mellin statement uses the upstream integral on `Re(s) > 2`.
The coefficient is the upstream twisted residue-class Mangoldt weight; this
does not assert the corresponding untwisted Mangoldt growth estimate.

`InfoGeometryGRH.RealDoubledGRH` applies the actual Dirichlet and centered-Xi zero
statements to the native real doubled readouts. The scalar readout is exactly
the multiplication operator for the corresponding analytic value. The
coordinate hypotheses and nontrivial-zero restrictions remain explicit.

The detailed theorem/normalization contract is in
[`docs/GRH_COMPATIBILITY_CONTRACT.md`](../../docs/GRH_COMPATIBILITY_CONTRACT.md).

## Reproduce verification

Use Python 3.11 or newer and install both named Lean toolchains with elan. From
the repository root:

```sh
python3 integrations/grh/verify_sources.py
python3 -m unittest discover -s integrations/grh -p test_audit_axioms.py
python3 integrations/grh/validate.py --cache
```

The last command takes the repository's shared build lock and runs the native
lane followed by the external lane. `--lane native` and `--lane external` select
one complete lane. Each lane verifies the actual `lean --version`, the checked
out dependency revisions and clean source state, compiles its exact targets,
and runs a fresh Lean axiom audit. `--cache` downloads pinned Mathlib artifacts;
it never deletes caches or updates dependency revisions. The default worker
bound is `LEAN_NUM_THREADS=2`.

When using standalone runtimes, provide the matching executables explicitly:

```sh
python3 integrations/grh/validate.py --lane external \
  --external-lake /absolute/path/to/lean-4.35.0/bin/lake
```

`--native-lake` and `GRH_NATIVE_LAKE` select the native executable;
`--external-lake` and `GRH_EXTERNAL_LAKE` select the external executable.
Every invocation runs from its owning package directory, allowing elan to
select that package's toolchain. An executable with the wrong version fails.
Builds use Lake's `--rehash` flag to check source contents when reusing build
traces. The external lane first builds the package-qualified `GRH/+New.Main`
target, then the adapters, so the logs distinguish upstream build failures
from adapter failures. This intermediate build is not a completed trust audit.

## Evidence and scope

The ignored `artifacts/native/` and `artifacts/external/` directories contain
build logs, compiler version, source hashes, dependency pins, the actual Lean
audit exit code, and parsed declaration counts. A successful build alone is
insufficient: the fresh audit must cover all eleven native owners, or all fourteen
owners in the external lane, and every recorded transitive axiom must belong
to `{propext, Classical.choice, Quot.sound}`. Missing summaries, proof holes,
custom axioms, unsafe/partial declarations, and inconsistent counts fail the
gate. Source fingerprints must remain unchanged throughout validation.

The GitHub workflow runs the native job first and the external job only after
it succeeds. Separate runners keep incompatible dependency caches apart. The
external job allows 330 minutes for the full readable proof. Only successful
trusted main pushes or manual runs save caches; pull requests can restore
those artifacts. A fresh axiom audit runs even after a cache hit.
The repository's cache policy keeps pull requests restore-only, including
same-repository pull requests. Consequently, a cold pull-request runner may
need to rebuild upstream GRH after an adapter failure; neither an intermediate
build nor that performance cost relaxes the cache policy or the final audit.

The root post-build gate retains its existing checks and adds this dedicated
route when an integration file or canonical import dependency changes. A native
lane pass establishes focused compatibility with the root pin; it does not
certify unrelated root targets. Legacy Lean 4.35 module-migration warnings are
retained in logs and do not relax the no-holes or axiom checks.

No prebuilt GRH proof was found in the upstream releases or workflow/check-run
records for the selected commit. The workflow therefore builds that dependency
from the pinned source after obtaining the official Mathlib cache.
