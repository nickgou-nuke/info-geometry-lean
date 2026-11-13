# Real matrix decomposition and metric adjoints

This package checks the canonical `lean/` sources for the real matrix split,
its bilinear interpretation, the ordered normality defect, metric-relative
adjoints, and the supplied two-dimensional example. It also checks the two
existing owners whose imports are narrowed for reuse.

## Sources

| Module | Role |
| --- | --- |
| `OperatorAlgebra.RealMatrixSplit` | Native half formulas, square expansion, normality/commutator equivalence, congruence covariance |
| `OperatorAlgebra.RealMatrixSplitGeometry` | Native bilinear split, symmetry, alternation, and even-dimensional obstruction |
| `OperatorAlgebra.RealMatrixSplitExamples` | Exact `Fin 2` example, positivity, nondegeneracy, noncommutation, and failed complex compatibility |
| `OperatorAlgebra.RealMetricAdjoint` | Raised-index operator and native predicates for the existing weighted adjoint |
| `Physics.FiniteMetriplecticMatrixSplit` | Bridge from the established Physics split to the native Mathlib maps |
| `OperatorAlgebra.WeightedAdjointCompatibility` | Existing generic weighted-adjoint owner |
| `Physics.FiniteMetriplecticDynamics` | Existing split, reconstruction, and uniqueness owner |

Every module name above has the prefix `InfoGeometry.`. The detailed intake,
hypotheses, dependency order, and scope are recorded in
[`docs/REAL_MATRIX_SPLIT_CONTRACT.md`](../../docs/REAL_MATRIX_SPLIT_CONTRACT.md).

## Reproduce the focused check

Run from the repository root with the pinned Lean toolchain on `PATH`:

```bash
python3 verification/real-matrix-split/audit.py
python3 verification/real-matrix-split/check.py build
python3 verification/real-matrix-split/check.py env lean lean/InfoGeometry/OperatorAlgebra/RealMatrixSplitAudit.lean > /tmp/real-matrix-split-axioms.log
python3 verification/real-matrix-split/audit.py --log /tmp/real-matrix-split-axioms.log
```

For a new checkout, retrieve Mathlib's pinned artifacts through
`python3 verification/real-matrix-split/check.py exe cache get` before the
build. No dependency update is required. The focused manifest contains the
same exact Mathlib and transitive Git revisions as the root manifest.

`check.py` acquires `/tmp/info-geometry-build.lock`, uses the maintained
workspace-integrity checks, and preserves existing build artifacts.
`RealMatrixSplitAll` is the import root; `RealMatrixSplitAudit` is a separate
command target. Source changes are compiled by ordinary Lake dependency
tracking. The fresh `env lean` invocation ensures that axiom output is
regenerated even when the build target is already current.

## Audit coverage

`audit.py` checks the explicit public declaration inventory for all seven
mathematical owners. It regenerates the audit with `--write`, checks focused
dependency pins against the root, and rejects forbidden proof constructs in
those sources. The axiom-log checker requires exactly one record per inventoried
head and accepts only `propext`, `Classical.choice`, and `Quot.sound`.

This is a bounded source inventory, not a Lean parser. Private helpers and
compiler-generated declarations are not separately enumerated; dependencies
of referenced helpers are included transitively by `#print axioms`.
Compilation, static screening, and independent semantic review are separate
checks. Five simple algebraic map laws may be reported as heuristic
`trivial_surface` warnings; they require review of their actual statements.

The checked-in workflow repeats the focused build and audit and uploads the
build, axiom, and checked-revision logs. A successful focused check does not
certify the root package, mirrored `src/` lane, every historical owner, or a
smooth symplectic/Kähler manifold construction.
