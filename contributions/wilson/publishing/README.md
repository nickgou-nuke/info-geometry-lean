# Focused upstream validation files

Each independent contribution patch includes its one workflow from the table
below and the identical shared script `.github/scripts/check_lean_axioms.py`.
Paths in this directory are already relative to the upstream repository root.

| Contribution | Workflow | Focused build target |
| --- | --- | --- |
| Weighted Gaussian elimination | `.github/workflows/weighted-gaussian.yml` | `GaussianBlockSpin.WeightedCoarseGrainingAudit` |
| Cutoff comparison estimates | `.github/workflows/cutoff-comparison.yml` | `CoreLean.CutoffCheck` |
| Positive kernel finite colimit | `.github/workflows/positive-kernel-colimit.yml` | `CoreLean.PositiveKernelFiniteColimitAudit` |
| Approximately compatible states | `.github/workflows/approximate-state-limits.yml` | `CoreLean.ApproximateStateLimitsAudit` |

The workflows run on affected pull-request paths or manual dispatch, with
read-only repository permissions and checkout credentials disabled. They use
the destination project's checked-in `lean-toolchain` and Lake configuration,
obtain Mathlib's cache, and build only the corresponding audit dependency
closure with `lake --wfail build`. They then invoke `lake env lean` on the audit
source to obtain a fresh transcript.

The shared checker extracts the exact explicit `#print axioms` inventory from
the audit source after removing comments. It rejects an empty or duplicate
inventory, missing or unexpected reports, duplicate reports, and any axiom
outside `propext`, `Classical.choice`, and `Quot.sound`. The resulting JSON
includes the audit source and transcript hashes.

Each workflow archives the checkout revision, actual Lean/Lake version output,
cache/build/axiom logs, audit JSON, and before/after copies of the dependency
configuration. Every existing pin/configuration file must remain byte-for-byte
unchanged. A newly resolved `lake-manifest.json` is permitted when the project
does not already track one, as is currently the case for GaussianBlockSpin;
that resolved manifest is included in the evidence.

Coverage is the selected contribution and its transitive imports. These jobs
do not compile the umbrella library or claim a whole-repository build.

## Author checks

The Python source parsed successfully. A bounded checker exercise accepted
multiline reports and declarations without axioms, and rejected six invalid
transcripts: missing, unexpected, duplicate, `sorryAx`, custom-axiom, and empty
output. All four workflows parse as YAML, and their embedded shell scripts
pass `bash -n`.

All four contributions passed the destination-pin preparation workflow in
[run 45571203500](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45571203500).
That workflow uses the same focused Lean audit targets, checks the exact
source inventories and dependency pins, and archives the fresh audit logs.
The upstream PR workflows themselves have not run on the upstream repository:
a writable fork is still required before the prepared branches can be pushed
and the four PRs opened. See [verification and publication status](../validation/STATUS.md).
