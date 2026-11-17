# Verification: real currents and projected associator dissipation

## Acceptance status

**Native acceptance is pending a repaired-head rerun.** The first exact-head
workflow, [44058874892](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44058874892),
reached native compilation at commit
`4625e30cc8635797e74dad50269cc9b9e2acafd1` and failed. It found five proof/API
errors in `HestenesCurrentAlgebra`, an over-simplified quaternion norm goal in
`SplitOctonionScalarPotential`, and a missing definition unfolding in
`SplitOctonionProjectedDissipation`. `HestenesCurrentGeometry` was blocked by
its algebra dependency. The selected files also produced 22 warnings.

The repair preserves theorem conclusions and the full mathematical carriers.
It fixes the actual pinned APIs,
ordered scalar-action rewrites, explicit graded membership and definition
unfolding, and removes the exact reported unused arguments/section assumptions.
The failed run's artifact was downloaded, SHA256-verified against GitHub, and
inspected against the published source hashes; its archive SHA256 is
`3b963d4cdae0e3dc3b63359908e5cd0b2eebc6b78aa6588ab122787b6ff29acb`.
A new exact-head run must compile all owners and complete the native axiom audit
before acceptance. Publication remains a draft while that evidence is pending.

The local nonblocking build-lock preflight again found the repository's shared
lock occupied by a `clifford-dirac` process. No competing compiler or cache
hydration was started, and the lock was not deleted, replaced, or bypassed.
The upstream workflow provides an independent runner while preserving the same
lock discipline.

## Second native run and warning repair

The repaired-head run,
[44087782634](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44087782634),
compiled all **55 repository modules** successfully at commit
`ebfd3b1faff4fa2bda62c4ab0b44d51154abdf73`, with no reused repository artifacts.
The maintained native checker reported `passed`, and its audit checked **144
declarations**, including generated declarations, with only
`propext`, `Classical.choice`, and `Quot.sound`.

| Selected owner | Compile exit code | Warnings | Audited declarations |
|---|---:|---:|---:|
| `HestenesCurrentAlgebra` | 0 | 0 | 47 |
| `HestenesCurrentGeometry` | 0 | 1 | 18 |
| `SplitOctonionScalarPotential` | 0 | 0 | 16 |
| `ProjectedOnsagerGram` | 0 | 1 | 28 |
| `SplitOctonionProjectedDissipation` | 0 | 2 | 35 |

The overall workflow still **failed** its separate selected-owner zero-warning
gate. Geometry reported an unused `Complex.star_def` simp argument. The other
three warnings concerned unused section instances in `projectedGram_symmetric`,
`associatorMatrix_mulVec_eq_zero_iff`, and `associatorGram_energy`.

The warning repair removes that unused simp argument and locally omits those
unneeded instances. It also omits `DecidableEq m` in the two dependent energy-rate
corollaries that no longer use the instance after the symmetry theorem's repair.
The mathematical conclusions, noncommutative order, full carriers, dependency
pins, maintained checker, and zero-warning acceptance rule are preserved. The
new source head still requires a fresh native run; the preceding head's native
result is not relabeled as a verification of the changed source.

Artifact `14333161691` was downloaded and matched GitHub's complete ZIP SHA256:
`82a04eb6172a5125e10cf52731b3eff437ccb6f1c7b68ada422393f38dd97af0`.
All 55 uploaded repository source snapshots match the reported hashes and exact
Git blobs at the verified head. The 63 complete evidence-manifest entries match.
The remaining `checker.log` entry matches its first 4,033 bytes; the uploaded
4,170-byte log also includes the zero-warning guard's subsequent traceback.
The archive digest verifies the complete uploaded bytes.

## Exact source scope

The selected owners are:

| Module | Theorem/lemma declarations | Definitions | Abbreviations |
|---|---:|---:|---:|
| `InfoGeometry.Canonical.HestenesCurrentAlgebra` | 36 | 5 | 0 |
| `InfoGeometry.Canonical.HestenesCurrentGeometry` | 12 | 2 | 0 |
| `InfoGeometry.Canonical.SplitOctonionScalarPotential` | 12 | 0 | 0 |
| `InfoGeometry.Physics.ProjectedOnsagerGram` | 17 | 3 | 0 |
| `InfoGeometry.Canonical.SplitOctonionProjectedDissipation` | 13 | 8 | 1 |
| **Total** | **90** | **18** | **1** |

This is a lexical inventory of source declarations, including private helpers.
The native environment's count, which also includes generated declarations, must
come from the axiom audit and is not inferred from this table.

The maintained source-closure resolver finds **55 repository modules** and
**49 directly referenced Mathlib source roots**. The closure includes the existing
`DAG.Basic` owner and the corrected canonical Physics imports of
`Canonical.ChiralCausalCone`. No source mirroring, skipped dependency, or checker
modification is used to resolve the archived `proofs.*` imports.

## Completed checks

The following source checks passed on the five new modules and the repaired
`ChiralCausalCone` dependency:

- Strict placeholder audit: no placeholder or custom-axiom violation.
- Semantic-vacuity gate at error severity: no errors.
- Strict OpenGauss screener: no violations.
- Whitespace/diff check.

The semantic heuristic reports eight warnings: six short coordinate/operator
interface or normalization results in the new modules, plus two pre-existing
declarations in `ChiralCausalCone`. Their bodies were inspected. They are not
unproved physical statements or structures assuming their desired conclusions.

Two initial heuristic operator-tactic flags in the scalar time-coordinate proofs
were resolved by using the native `Complex.mul_conj` norm identity and a direct
nonzero inequality lemma. The screener itself was not changed.

Independent source/API review covered all five modules, including the actual
noncommutative multiplication order, the scalar/pseudoscalar sign, faithful
grade-one current identification, positive time normalization, normalized-axis
projector hypotheses, the zero-energy projector convention, and the concrete
nonzero associator-production witness. It also checked the canonical import
replacement and downstream namespace consumers.

The workflow passed YAML parsing, syntax checks of its four shell blocks, AST
parsing of its three embedded Python blocks, and exact target/path coverage
checks. Independent review covered source-head binding, pins, archive verification,
fresh repository outputs, lock inheritance, audit enforcement, warning checks,
and read-only permissions. These are source checks, not workflow execution.

The installed `.githooks/pre-commit` runs the repository's maintained
`proof_proxy_staged_gate.py` on the commit. Its actual outcome is recorded with
the publication evidence; it is not a substitute for native compilation.

## Upstream native workflow

[current-associator.yml](../.github/workflows/current-associator.yml) verifies the
exact pull-request head, rather than a moving branch or synthetic merge commit.

1. Fetch and verify the requested source commit.
2. Require the unchanged repository pins: Lean `4.34.1` and Mathlib
   `d13f23b723b8a846827a245b89c10fc7d3f11612`.
3. Restore or download the Lean distribution archive, verify its SHA256 on every
   run, and extract it into an uncached runtime directory. The archive digest is
   `47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4`.
4. Hydrate the current Mathlib import roots under the repository's shared lock.
   Only pinned dependency artifacts are cached; repository `.olean` files are
   never restored.
5. Invoke the unchanged `tools/quality/check_clifford_dirac.py` on the five owners
   and their complete repository source closure, using fresh attempt-specific
   outputs and no incremental or skip-audit mode.
6. Run the maintained native declaration audit. It inspects all declarations
   owned by the five selected modules, including generated declarations, and
   permits only `propext`, `Classical.choice`, and `Quot.sound`. Unsafe and partial
   selected declarations are rejected.
7. Require a passed report with the exact head and target list, successful
   compilation, and zero warnings for every selected owner.
8. Upload logs, source snapshots, hashes and reports even if verification fails.

The workflow has only `contents: read` permission. Neither its source inspection
nor a queued workflow constitutes native acceptance. Any compiler failure must be
repaired and rechecked at the resulting new source head before acceptance.

## Limits

This check is scoped to the selected owners and their import closure. It does not
certify the whole root Lake package, whose separately observed unresolved path
packages include `external_refs/homotopy-hypothesis-lean4` and
`external_refs/atlas-lean`. No dependency pin is invented or changed to hide those
root-level obligations.

The formalization does not supply a Dirac PDE solution or Cauchy-charge theorem,
a general observer-flux functional, a curved para-Kähler manifold or
Monge–Ampère solution, a Gibbs integrability theorem for an unspecified orbit,
or a reservoir/erasure model proving a Landauer heat law. The exact mathematical
scope and correction ledger are in
[CURRENT_ASSOCIATOR_CONTRACT.md](CURRENT_ASSOCIATOR_CONTRACT.md).
