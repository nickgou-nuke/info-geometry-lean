# Unified operator bridges: validation

Date: 2026-11-19. Repository source base:
`fea96b564201654cd4693008585039a56f66adf3`.

Status: **local native and source-gate acceptance passed**. Source review is
recorded separately from the kernel evidence below. The actual commit must also
pass the installed pre-commit hook, and published-head CI is reported on the PR.

## Scope and environment

The acceptance scope is the five new modules below and their complete local
import closure. The maintained checker computes that closure from actual imports,
copies the source bytes into a separate build directory, checks the pinned
dependency revision, and generates a fresh audit of every declaration owned by
the five targets.

- Lean toolchain: `leanprover/lean4:v4.34.1`.
- Native Lean commit: `5045d0056413266e57c625dcd7c365b10e377c52`.
- Mathlib revision: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Repository closure: 25 modules.
- Build coordination: the maintained shared `BuildLock`; no parallel compiler
  process bypasses that lock.
- Acceptance requires fresh compilation and a fresh axiom audit. Incremental
  reuse was allowed only during error repair, with matching source fingerprints.

## Independent source review

The cyclotomic author and information-geometry author reviewed each other's
integrated modules. A separate runtime agent performed native verification and
source gates without editing the proofs. The root-authored contract, literature
ledger, workflow, and preserved intake received independent agent source review.
These reviews are distinct from the Lean kernel audit.

| Target module | Reviewed SHA-256 |
| --- | --- |
| `InfoGeometry.OperatorAlgebra.CyclotomicGradedAdjoint` | `09e09a920c262e7646a10647c1144d3f24ca3f7f9754ccc83a2ac0a9bd403c0c` |
| `InfoGeometry.OperatorAlgebra.InternalCyclotomicGradedAdjoint` | `bf85bcfb28641c5db2c6833386944fac50ba2cd89fbe0be99c6f295551f86e23` |
| `InfoGeometry.OperatorAlgebra.RealCubicAdjointWitness` | `7a7ba2f479d584f9576c2c5a420825266b7a1c9605fed6e8cbf19a2c5a8ce0f4` |
| `InfoGeometry.Geometry.MixedPairingNondegeneracy` | `19d55e13c74f2b66f470fc2940f1efee34637a7a840b4ad3f5fd34cda2b418df` |
| `InfoGeometry.InformationGeometry.ContrastMixedHessianBoundary` | `3f2c79f0ece723e09b75b2d0183e6dc26073f2e96d3ece5a1e92a9f2aad102b6` |

The original attachment is preserved byte for byte: 12,155 bytes, SHA-256
`ad0e42944eb1e912d996e37b56add897fa0184ad8d0c294ef86a59e26ac23934`.
Its manifest labels the content as claims to audit, not execution evidence.

## Native acceptance

The final local native report has status `passed`: **25 repository modules
compiled without reuse**, and every target compiled with zero warnings. The
fresh audit contains **110 owned declarations**, with aggregate axiom list
exactly `[propext, Classical.choice, Quot.sound]`.

| Selected owner | Audited declarations | Native warnings |
| --- | ---: | ---: |
| `CyclotomicGradedAdjoint` | 16 | 0 |
| `InternalCyclotomicGradedAdjoint` | 5 | 0 |
| `RealCubicAdjointWitness` | 36 | 0 |
| `MixedPairingNondegeneracy` | 17 | 0 |
| `ContrastMixedHessianBoundary` | 36 | 0 |

The report SHA-256 is
`ab0122e457c8891b2176fe73f61ab909aa10cd62d8110101e05826cb4cb05da1`.
Its full source-hash inventory matches the checked working-tree bytes, including
all five hashes above. The complete module set, dependency map, dependency pin,
toolchain, declaration counts, and axiom list were reconciled. No audit-skipping
or incremental option was used for this acceptance run.

Local acceptance ran before the new commit, so the report's `local_revision`
is the recorded base revision. The checked new sources are identified by their
content hashes; the report does not claim they already existed in that base
commit. The dedicated Actions workflow repeats verification at the published
PR head and requires its report revision to match that exact head.

The final run recorded **29 warnings in unchanged dependencies**: five in
`Quantum.SylvesterWeylBraidBridge`, one in `Clifford.SplitQ11`, two in
`Geometry.MoebiusChiralGeneratorClassification`, three in
`Algebra.MatrixCyclotomics`, and eighteen in `Physics.HestenesKreinOperatorCalculus`.
Their per-module counts remain visible in the report. No unrelated dependency
or maintained warning policy is changed by this PR.

## Maintained source gates

All five exact target paths passed the maintained gates:

- Strict placeholder audit.
- Semantic-vacuity audit with complete path and read coverage.
- OpenGauss strict refutation and static `GATE_4` review.
- Strict proof-source checking of every indexed target, including equality of
  indexed bytes and working-tree bytes and stability of the index tree.

Each gate exited successfully. The source gates used the same bytes as the native
run; all five indexed files were explicitly covered, their bytes matched the
working tree and native inventory, and the index tree remained stable during the
checks. The strict actual-staged invocation also passed. Gate and verification
helper hashes were reconciled against the unchanged repository implementations.

The final local commit runs the installed `.githooks/pre-commit` normally. That
commit hook is an additional publication step, not replaced by the explicit
indexed-content check or by this document.

OpenGauss static review is not represented as native kernel verification. The
separate maintained native checker provides the compilation and axiom evidence.

## Reproduction and PR evidence

With the pinned toolchain and Mathlib checkout, run the unchanged checker with a
fresh evidence directory:

```sh
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root "$UNIFIED_MATHLIB_ROOT" \
  --output "$UNIFIED_EVIDENCE_DIR" \
  --target InfoGeometry.OperatorAlgebra.CyclotomicGradedAdjoint \
  --target InfoGeometry.OperatorAlgebra.InternalCyclotomicGradedAdjoint \
  --target InfoGeometry.OperatorAlgebra.RealCubicAdjointWitness \
  --target InfoGeometry.Geometry.MixedPairingNondegeneracy \
  --target InfoGeometry.InformationGeometry.ContrastMixedHessianBoundary
```

The dedicated `unified-operator-bridges.yml` workflow checks the actual PR head,
not a synthetic merge source. Its trigger list covers the full repository closure,
and the job checks that coverage against the imports. It reconciles the complete
native report and runs the maintained source gates on all five indexed targets,
even though the CI checkout has no staged diff. It binds the workflow, helper
sources, dependency pins, contract, literature ledger, this record, and original
intake to an evidence digest index. The uploaded artifact is named
`unified-operator-bridges-kernel-evidence`.

This document records local acceptance. The PR's Actions run and its matching
source revision provide the published-head result; this document does not assert
that a future run has already passed.

## Limits

The audit covers these five owners and their imports, not a full repository build.
The bibliography and bounded owner search are separate source review; the existing
BKM, Berezinian, and other referenced modules are not silently added to the native
acceptance scope. The new results do not assert global para-Kähler geometry, an
arbitrary Jones tower, a quantum super-Grassmannian equivalence, or a universal
identification of cyclotomic roots with nilpotent operators.
