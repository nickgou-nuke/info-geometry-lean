# Native finite C-star and SLD foundation

The new modules extend existing owners rather than replace the categorical
inductive-system or state definitions.

- `Canonical/CStarMatrixTowerIsometry.lean` proves injectivity, isometry, norm
  preservation, and strict trace positivity for the existing `CStarMatrix`
  transition maps. The native operator norm is used, not an arbitrary matrix norm.
- `QuantumGeometry/SLDLyapunov.lean` proves existence and uniqueness of the SLD
  for every finite positive-definite density matrix and arbitrary matrix
  variation. It uses the native spectral theorem; variations need not commute
  with the density. Hermitian variations have Hermitian SLDs.
- `QuantumGeometry/SLDTraceMetric.lean` constructs the bijective Lyapunov linear
  map and its actual inverse, proves the inverse solves the SLD equation, and
  proves symmetry and nonnegativity of the finite tangent metric.
- `OperatorAlgebra/SpinorMetric.lean` proves symmetry and nonnegativity of state
  anticommutator forms and strict positivity for the faithful finite trace state.
- `OperatorAlgebra/StateTangentVector.lean` constructs the closed real submodule
  of `StrongDual ℂ Algebra` consisting of star-preserving functionals vanishing
  at one, with inherited normed and complete-space instances.
- `OperatorAlgebra/SpinorMetricDependency.lean` separates the tower-isometry,
  positive-density/SLD, and Banach-dual branches in a finite partial order.

The Bures convention here is one quarter of SLD quantum Fisher information:
`(1 / 4) * Re (trace (X * SLD(Y)))`. The proposed one-half prefactor is a
different normalization. The native positive normalized state is reused;
nonnegativity of only the real part is not substituted for complex positivity.

No general C-star state is identified with a density element via GNS. No claim
is made that faithful infinite-dimensional states form an open manifold, that
the closed affine-constraint subspace is already its tangent bundle, or that
the Bures geometry is dually flat. The existing represented completion owners
are not replaced by a raw ring quotient with an unconstructed norm. These
positive statistical forms do not replace the repository's indefinite Krein
metric or identify a fundamental symmetry with modular conjugation.

Validation: all six production modules and `SpinorMetricTests.lean` pass the
isolated Lean 4.28.0 checker using the cached Mathlib revision matching the root
manifest. Fifteen printed axiom audits contain only standard Lean axioms, with
no `sorryAx`. Tests include a noncommuting qubit SLD and nonexistence at a
singular zero density for nonzero variation. These earlier checks are not
acceptance under the required Lean 4.28.1. Pinned dependencies are now being
rebuilt from source with 4.28.1; this module group still needs its own rerun.
Whole-repository compilation is not claimed.
