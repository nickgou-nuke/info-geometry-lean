# Support-Restricted Relative Modular Hamiltonian Lane Map

## Lane Intent

Owner order is preserved:

1. `Δ` is primary.
2. `K := -log Δ` is derived.
3. support/domain handling is explicit.

This lane adds a finite support surrogate for domain-aware Hamiltonians without
over-claiming unbounded functional calculus.

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

