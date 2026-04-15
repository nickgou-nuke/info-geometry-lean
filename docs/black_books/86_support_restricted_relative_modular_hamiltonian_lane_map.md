# Support-Restricted Relative Modular Hamiltonian Lane Map

## Lane Intent

Owner order is preserved:

1. `Δ` is primary.
2. `K := -log Δ` is derived.
3. support/domain handling is explicit.

This lane adds a finite support surrogate for domain-aware Hamiltonians without
over-claiming unbounded functional calculus.

## Canonical Support Mechanism (Type III Root)

At the modular-theory root, support handling is spectral, not inverse-based:

- support projector: `s(Δ) = 1_(0,∞)(Δ)`,
- Hamiltonian domain: `K := -log Δ` defined on `s(Δ)`,
- mechanism: spectral projection + functional calculus.

So the `Δ -> log Δ` transition is a support-restricted spectral logarithm.
No Moore–Penrose or Drazin inverse is required at this canonical root layer.
Equivalently: functional calculus defines `log Δ` spectrally; support selects
the valid domain.

## Repo-Translated Implementation Lane (Doubled Carrier)

In this repository, singular/support-sensitive structure is intentionally
translated into the doubled real/Krein operator package through certified
projector owners:

- Drazin lane: `P_reg = Δ Δ^D`, `P0 = 1 - P_reg` (spectral/algebraic support),
- Moore–Penrose lane: `P_R = Δ Δ⁺`, `P_L = Δ⁺ Δ` (metric/self-adjoint support),
- anomaly lane: `χ = [P_D, P_L]`.

This is not "two different supports" at ontology level. It is one abstract
support with two inequivalent realizations after translation into the doubled
carrier:

- Drazin realization preserves the functional-calculus lane (commutes with `Δ`),
- Moore–Penrose realization preserves metric/self-adjoint closure.

Their mismatch commutator is interpreted as the obstruction to simultaneous
spectral and geometric diagonalization.

These are load-bearing in the repo's translated operator grammar and do not
replace the canonical Type III root mechanism above.

Operational rule:

1. root narrative: support projection of `Δ` + functional calculus;
2. translated finite/operator implementation: Drazin/Moore–Penrose projector
   package on the doubled carrier.

Execution semantics for the modular generator lane:

`K = -log(Δ|_{P_reg})`

where log is spectral, and projector data realizes the admissible sector
inside the repo's doubled/Krein operator algebra.

## Theorem Status

- `REPO_THEOREM`: compiled in Lean.
- `NEXT_OWNER_TARGET`: not yet in owner files; requires new formal module.
- `RESEARCH_INTERFACE`: abstract interface only.

## A. Finite Support Owner (now compiled)

- `REPO_THEOREM`
  [`supportRestrictedModularHamiltonianOperator`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularHamiltonianSupport.lean:37)
- `REPO_THEOREM`
  [`supportRestrictedModularHamiltonianOperator_eq_supportProjector_mul`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularHamiltonianSupport.lean:59)
- `REPO_THEOREM`
  [`supportRestrictedModularHamiltonianOperator_eq_mul_supportProjector`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularHamiltonianSupport.lean:76)
- `REPO_THEOREM`
  [`supportRestrictedModularHamiltonianOperator_univ`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularHamiltonianSupport.lean:116)
- `REPO_THEOREM`
  [`supportRestrictedModularHamiltonianOperator_empty`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularHamiltonianSupport.lean:130)
- `REPO_THEOREM`
  [`supportRestrictedModularHamiltonianOperator_cocycle`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularHamiltonianSupport.lean:139)

## B. Existing Upstream Owners (already stable)

- `REPO_THEOREM`
  [`relativeModularOperator_cocycle`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularOperator.lean:168)
- `REPO_THEOREM`
  [`relativeModularHamiltonianOperator_cocycle`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularHamiltonian.lean:95)
- `REPO_THEOREM`
  [`finite_commuting_lift_package`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularCommutingLift.lean:90)

## B2. Projector-Controlled Execution Invariants (now compiled)

- `REPO_THEOREM`
  [`regularRestrictedSuperHamiltonian`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/DrazinSupercharge.lean:245)
- `REPO_THEOREM`
  [`spectralProjector_mul_regularRestrictedSuperHamiltonian`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/DrazinSupercharge.lean:259)
- `REPO_THEOREM`
  [`regularRestrictedSuperHamiltonian_mul_spectralProjector`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/DrazinSupercharge.lean:278)
- `REPO_THEOREM`
  [`regularRestrictedSuperHamiltonian_fixed_under_spectralGradingFlow`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/DrazinSupercharge.lean:434)
- `REPO_THEOREM`
  [`defectCompression_regularRestrictedSuperHamiltonian_eq_zero`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/DrazinSupercharge.lean:334)
- `REPO_THEOREM`
  [`regularRestrictedSuperHamiltonian_support_flow_package`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/DrazinSupercharge.lean:488)

## C. Immediate Next Owner Targets

- `NEXT_OWNER_TARGET`
  commuting positive-operator theorem surface for
  `log (A * B) = log A + log B` under explicit `Commute A B`.
- `NEXT_OWNER_TARGET`
  bridge from support-restricted finite Hamiltonian to bounded operator API
  abstraction.

## D. Research Interface (not yet owner)

- `RESEARCH_INTERFACE`
  affiliated unbounded `K := -log Δ` on `supp Δ`.
- `RESEARCH_INTERFACE`
  Connes-cocycle to relative modular operator owner bridge in Type III core.
- `RESEARCH_INTERFACE`
  full Pedersen–Takesaki / Vaes RN operator layer as canonical owner files.

## Build Gate

Required green targets for this lane:

```bash
lake build InfoGeometry.Canonical.RelativeModularHamiltonianSupport
lake build InfoGeometry.Canonical.All
lake build InfoGeometry.All
```
