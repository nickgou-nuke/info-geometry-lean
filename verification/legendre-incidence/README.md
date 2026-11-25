# Focused Legendre, incidence, and operator validation

This package compiles four canonical mathematical owners and a generated
declaration audit without importing a broad repository umbrella. It uses the
root `lean-toolchain` and all nine pinned Mathlib dependency revisions. The
project reads the canonical files under `lean/`; it contains no copied proofs.

## Mathematical scope

- `InfoGeometry.Twistor.FenchelContactIncidence`: the exact Fenchel gap as a
  homogeneous incidence defect; a nonzero native dyad, contact, and its
  canonical Peirce projector; actual convex derivative attainment.
- `InfoGeometry.Geometry.LegendreGraphGeometry`: graph orthogonality,
  maximal isotropy, dimension, actual derivative ranges, native Grassmannian
  points, incidence, and Schwarz symmetry for an actual local C² potential.
- `InfoGeometry.Geometry.CotangentOperators`: contragredient graph transport,
  a faithful native cotangent Lie homomorphism, form invariance, graph
  preservation, and exact algebraic Hamiltonian tangent identities.
- `InfoGeometry.Twistor.FenchelContactTransport`: the actual moving grading,
  a nonzero nilpotent graded derivation, coordinate covariance, transport of
  the actual Fenchel conjugate, and an explicit reference-cut transvection.

The source audit and exact theorem contracts are in
[`docs/LEGENDRE_INCIDENCE_OPERATOR_AUDIT_20261124.md`](../../docs/LEGENDRE_INCIDENCE_OPERATOR_AUDIT_20261124.md).
These are local analytic and algebraic constructions. A global supermanifold,
integrated Hamiltonian flow, a physical supercharge pair, and a quantization
map require additional theorems.

## Reproducible commands

Use Python 3.11 or newer on a POSIX system (the maintained lock uses `fcntl`).
From an independent checkout with the pinned Lean toolchain available:

```bash
set -euo pipefail
python3 verification/legendre-incidence/audit.py
python3 verification/legendre-incidence/check.py exe cache get
python3 verification/legendre-incidence/check.py build
python3 verification/legendre-incidence/check.py env lean lean/InfoGeometry/Twistor/LegendreIncidenceAudit.lean > legendre-incidence-axioms.log
python3 verification/legendre-incidence/audit.py --log legendre-incidence-axioms.log
```

The generated audit lists every explicitly declared public definition and
theorem in these four owners. The validator checks exact source coverage and
the actual Lean-reported axiom inventory, with each declaration reported
exactly once; only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
Regenerate it after changing the public inventory
with `python3 verification/legendre-incidence/audit.py --write` and compile it
again. A text scan or a generated audit file alone is not a kernel check.

`check.py` uses the maintained global build lock. It rejects linked worktrees,
symlinked Lake roots, and unrecorded local package overrides. After acquiring
the lock, it checks focused/root dependency agreement and the actual selected
Lean/Lake release, revision agreement, and runtime location. It hashes the
canonical source import closure and validation controls before/after the run
to reject changed inputs. Normal dependency artifact writes remain enabled.
Its default is to wait for the lock; use `--no-wait` to report a busy lock
without waiting.

An existing complete pinned package cache can be selected explicitly:

```bash
python3 verification/legendre-incidence/check.py --dependency-root /absolute/path/to/packages build
```

This validates each package's exact Git revision and clean tracked sources,
then uses Lake's native temporary package-location override. It does not edit
the tracked manifest, change a dependency revision, or link `.lake` roots.
Project outputs remain in this package's own `.lake/build`; normal generated
dependency artifacts may be refreshed under the same shared lock.

The source inventory scanner in `audit.py` is scoped to these owners' explicit
single-namespace declarations. The `--log` check must follow a successful Lean
exit, as in the workflow; parsing a supplied log alone does not prove that its
producer succeeded. Independent source reviews are preserved in [`reviews/`](reviews/).

The GitHub Actions workflow repeats the focused build, performs a fresh Lean
axiom-printing run, and preserves both logs. Its results certify the declared
import closure, not every tracked historical source file in the repository.
