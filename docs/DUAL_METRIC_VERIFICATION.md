# Verification: real dual metric compatibility

## Acceptance status

**Native compilation and the declaration axiom audit are pending.** These are
complete proposed Lean proofs with source and pinned-API review. The published
change remains a draft until its exact source head has passed the native
workflow and the resulting evidence has been inspected.

The local nonblocking preflight found the original shared build lock occupied
by a `clifford-dirac` transaction. No competing compiler, test, or cache
hydration was started, and the lock was not deleted, replaced, or bypassed.
The upstream workflow uses an independent runner with the same maintained
lock discipline.

## Exact source scope

| Selected owner | Theorem declarations | Definitions |
|---|---:|---:|
| `InfoGeometry.Geometry.SymplecticComplexParaCompatibility` | 13 | 0 |
| `InfoGeometry.Clifford.PositivePhaseMetricBridge` | 10 | 1 |
| `InfoGeometry.Examples.PositiveCompatibleNonAnticommuting` | 14 | 2 |
| `InfoGeometry.Canonical.SplitOctonionEllipticHyperbolicBridge` | 11 | 0 |
| **Total** | **48** | **3** |

This is an inventory of explicit source declarations. The native audit's count
also includes generated declarations and must come from its actual execution.

The unchanged maintained closure resolver finds **32 repository modules** and
**37 directly referenced Mathlib roots**. Every source path exists. All four
new owners have been integrated into the real repository; no candidate overlay
or supplied import list is used by the acceptance checker. The independent
workflow inventory agrees with the maintained resolver on module order,
dependencies, native roots, and source hashes.

No dependency pin, source-closure checker, native audit generator, shared lock,
or existing quality gate is modified by this change.

## Source verification

The required source checks cover all four owners:

```text
python3 tools/quality/placeholder_audit.py --root <owner.lean> --strict --json-out <report.json>
python3 tools/quality/semantic_vacuity_gate.py <four owners> --fail-on error --json-out <report.json>
python3 tools/infra/opengauss_screener.py <four owners> --strict --json
git diff --check
```

The strict placeholder audit and semantic error gate pass. Five nonblocking
semantic heuristics identify short coordinate readouts or direct reuse of
existing square/metric identities. Their statements and bodies were inspected;
they do not package an unproved physical conclusion as an input field.

The initial operator screener heuristically flagged four scalar bilinear-form
steps and an expanded scalar determinant calculation. The proof refinements
replace the former with direct native negation and order lemmas, and the latter
with the full matrix congruence `Kᵀ*(-I)*K = -(-I)` followed by
`Matrix.toBilin'_comp`. The strict screener then passes. The screener itself is
unchanged, and no theorem statement is weakened.

Independent source/API review covers all four owners, the shared-metric product
addendum, the cotangent sign convention, the real sheared-involution
counterexample, the actual quaternion multiplication order, and the explicit
associator witness. Review found and corrected a missing scalar commutativity
rewrite, two negated-subtraction normalizations, and unnecessary literal-vector
simplification arguments before publication.

The theorem contract was checked against the integrated statements, including
the exact minimal assumptions of the isometry/anticommutation equivalence and
the distinction between algebraic, dimensional, and differential claims.

Workflow source verification includes YAML parsing, syntax parsing of all four
Bash blocks, and AST parsing of all three embedded Python blocks. Its watched
paths cover the full 32-module closure. After the scope and target substitutions,
its job protocol matches the previously reviewed exact-head native workflow.
These are source/syntax checks, not an execution of the workflow.

The installed `.githooks/pre-commit` runs the maintained
`proof_proxy_staged_gate.py` at the publication checkpoint. Its actual outcome
is recorded with the commit evidence; the hook's presence alone is not a pass.

## Native workflow and evidence requirements

[dual-metric.yml](../.github/workflows/dual-metric.yml) performs these checks:

1. Fetch and verify the exact pull-request head, rather than a synthetic merge
   commit or a moving branch.
2. Require the unchanged Lean `4.34.1` and Mathlib
   `d13f23b723b8a846827a245b89c10fc7d3f11612` pins.
3. Verify the Lean distribution archive SHA256 on every run, including cache
   hits, then extract an uncached executable distribution. The archive digest is
   `47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4`.
4. Hydrate selected Mathlib imports under the original shared lock, with the
   lock descriptor inherited by subprocesses. Only pinned dependency artifacts
   are cached; repository compilation outputs are fresh.
5. Invoke the unchanged `tools/quality/check_clifford_dirac.py` with the four
   selected targets, their complete repository source closure, and native audit
   enabled. Neither incremental acceptance nor skipped audit is used.
6. Require the maintained native audit of every selected-owner declaration,
   including generated declarations. Only `propext`, `Classical.choice`, and
   `Quot.sound` are allowed. Unsafe or partial selected declarations are rejected.
7. Verify the report's exact head and target list, successful compilation of
   every selected owner, and zero selected-owner warnings.
8. Upload logs, reports, source snapshots, and provenance even after failure.

The workflow has read-only repository permissions. Its expected success is not
reported as observed success. Any failure requires diagnosis from that run and
a fresh check of the resulting repaired source head.

## Coverage boundaries

This is scoped verification of four owners and their imports. It does not
certify the whole root Lake package or every historical source file. The
separately observed root path-package obligations include
`external_refs/homotopy-hypothesis-lean4` and `external_refs/atlas-lean`.

The source establishes the stated real algebraic relationships. It does not
construct a curved Kähler or hypersymplectic manifold, establish a signature or
dimension classification, derive affine/Levi-Civita curvature, supply a
statistical model or normalizable Gibbs measure, or derive a full metriplectic
or Landauer heat law. The explanatory differential counterexamples are not
counted as newly formalized differential-geometry theorems.

See [DUAL_METRIC_CONTRACT.md](DUAL_METRIC_CONTRACT.md) for input provenance,
canonical-owner reuse, exact assumptions, and corrected implications.
