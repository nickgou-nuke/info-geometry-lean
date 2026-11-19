# Split spinor potential: verification record

Date: 2026-11-16. Base revision: `08c34e03f610b452e03422037949196dc7d92d6d`.
Branch: `codex/split-spinor-potential-20261116`.

## Native proof scope

The maintained `tools/quality/check_clifford_dirac.py` checker compiled the
exact repository source closure of seven selected targets and audited their
declarations with the native Lean kernel. The final check used trusted,
source-fingerprinted incremental reuse for unchanged dependencies and rebuilt
every changed Lean owner. Builds were serialized under the repository's shared
build lock.

The unchanged pins are:

- Lean: `leanprover/lean4:v4.34.1`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

| New module | Explicit theorems | Explicit definitions | Audited declarations | Warnings |
|---|---:|---:|---:|---:|
| `Clifford.ChevalleyNeutralCompatibility` | 13 | 0 | 17 | 0 |
| `Clifford.ParaKreinObstructions` | 7 | 0 | 7 | 0 |
| `Clifford.NeutralCotangentHamiltonian` | 16 | 3 | 27 | 0 |
| `Geometry.ParaPotentialPullback` | 16 | 4 | 28 | 0 |
| **New total** | **52** | **7** | **79** | **0** |

Audited declaration counts include compiler-generated declarations. They are
not theorem counts. The seven-target audit checks 159 declarations in total;
the repository source closure contains 33 modules. The three supporting targets
are `Geometry.ParaHessianMixedPotential`,
`Canonical.CartanSouriauMassieuDirectionalCalculus`, and
`Canonical.SouriauOnsagerBKMParaKahlerObstruction`.

The only axioms reported by the audit are `propext`, `Classical.choice`, and
`Quot.sound`. There are no new proof placeholders or custom axioms. The
unchanged dependency closure emits 44 existing warnings; the four new owners
emit none.

## Reproduction

Run from a checkout containing this patch, using the matching pinned Mathlib
checkout and native Lean executable:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /path/to/mathlib-4.34.1 \
  --lean /path/to/lean-runtime/bin/lean \
  --output /path/to/verification-output \
  --target InfoGeometry.Clifford.ChevalleyNeutralCompatibility \
  --target InfoGeometry.Clifford.ParaKreinObstructions \
  --target InfoGeometry.Clifford.NeutralCotangentHamiltonian \
  --target InfoGeometry.Geometry.ParaPotentialPullback \
  --target InfoGeometry.Geometry.ParaHessianMixedPotential \
  --target InfoGeometry.Canonical.CartanSouriauMassieuDirectionalCalculus \
  --target InfoGeometry.Canonical.SouriauOnsagerBKMParaKahlerObstruction \
  --incremental
```

The report records the Lean version, Mathlib revision, repository source
hashes, verifier source hashes, dependency graph, artifact hashes, declaration
counts, and axiom audit. Its `local_revision` is the base revision at the time
the task-owned working tree was checked; the per-source hashes identify the
actual checked additions.

## Source and semantic review

The four new owners were checked by the strict placeholder audit, semantic
vacuity gate, and strict OpenGauss source screener. The staged proof gate and
`git diff --check` were also run on the task-owned change set. Gate policies
and toolchain pins were not modified or bypassed.

Independent reviews checked operator order, existing declaration ownership,
native derivative hypotheses, the algebraic versus analytic Hessian boundary,
weak nondegeneracy, and the absence of an assumed Spin group moment map. The
initial proposed duplicate exterior representation was removed in favor of a
compatibility module using the existing full representation. Scalar arithmetic
after bilinear evaluation was made explicit to satisfy the operator-carrier
source guard without weakening any theorem statement.

## Limits of this certificate

This is a scoped native proof certificate, not a successful root Lake build or
a whole-repository `InfoGeometry.All` certificate. The four imports were added
to that aggregator, but the full aggregator was not compiled by this check.

`Thermo.GenericMetriplecticFlow` was inspected for its existing nondegenerate
Poisson/Casimir obstruction. It was not included in the successful native
scope: its aggregate `Mathlib` import requires an unavailable `Mathlib.olean`
in the scoped dependency cache. No unrelated import or pin was changed to
make that additional target build.

The following are mathematical analysis in the companion review, not new
kernel results: the Mukai parity table and its low-dimensional bases; the
explicit quantum matrix-exponential model; the full para-Kähler manifold
construction; normalizability and differentiation of a continuous Souriau
partition integral; prescribed-volume PDE existence; global Spin equivariance;
the proposed metriplectic extension; and the Landauer process identity.

The new pullback theorem proves the actual mixed derivative under explicit
native differentiability hypotheses. Its opposite-direction kernel theorem
is an algebraic identity for a pulled-back bilinear form, not a separate proof
of the full second Fréchet derivative. The Hamiltonian derivative is a native
real-line `HasDerivAt`; the arbitrary algebraic carrier has no imposed norm.
