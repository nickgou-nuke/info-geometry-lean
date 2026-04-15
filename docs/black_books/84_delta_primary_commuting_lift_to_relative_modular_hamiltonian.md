# Δ-Primary Commuting Lift to Relative Modular Hamiltonian

## Scope

This chapter fixes a strict boundary:

- finite diagonal/commuting lane is **proved**,
- unbounded Tomita–Takesaki and crossed-product Type III lanes remain **interface/research**.

No speculative equivalence is promoted to canonical theorem status.

## Canonical Lift Order

The owner order is:

1. `Δ` (relative modular operator) is primary.
2. `K := -log Δ` is derived by logarithmic readout.
3. scalar Hamiltonian readouts are shadows of the operator owner.

This is now encoded directly in Lean:

- [`RelativeModularOperator.lean`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularOperator.lean)
  - `relativeModularOperator`
  - `relativeModularOperator_cocycle`
- [`RelativeModularHamiltonian.lean`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularHamiltonian.lean)
  - `relativeModularHamiltonianOperator`
  - `relativeModularHamiltonianOperator_cocycle`
  - `relativeModularHamiltonianExpectation_eq_readout`
- [`RelativeModularCommutingLift.lean`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularCommutingLift.lean)
  - `relativeModularOperator_mul_comm`
  - `log_relativeModularOperator_diag_cocycle`
  - `finite_commuting_lift_package`

## What Is Proved Now

Inside the finite commuting spectral lane:

- multiplicative cocycle for `Δ`,
- diagonal `log Δ` additive cocycle,
- operator-level cocycle for `K = -log Δ`,
- commuting of any two finite relative modular operators.

This is the exact algebraic lift from diagonal spectral data to relative modular Hamiltonian **in the finite owner regime**.

## What Is Not Yet Proved

Not yet canonical in this repository:

- unbounded-domain `log Δ` calculus in full generality,
- Pedersen–Takesaki / Vaes affiliated-operator RN theorem stack as owner theorems,
- internal crossed-product construction for the Type III continuous core.

These remain explicitly tracked as interface/research surfaces (see coverage matrix below).

## New Formalization Lane (Chunk Map)

### Chunk A (closed)

Finite commuting owner lane:

- `RelativeModularOperator`
- `RelativeModularHamiltonian`
- `RelativeModularCommutingLift`

### Chunk B (next owner target)

Commuting positive-operator interface (bounded, support-aware):

- define a conservative owner API for positive commuting operators,
- prove `log(AB)=log A + log B` only under explicit commute + positivity hypotheses.

### Chunk C (next interface target)

Support/domain-aware Hamiltonian interface:

- `K := -log Δ` on support,
- explicit boundary between bounded finite lane and unbounded/interface lane.

### Chunk D (research lane)

Type III core realization:

- crossed-product/Haagerup density surfaces,
- cocycle-to-Hamiltonian bridge in the core representation.

## Build Check

Minimal check for this lane:

```bash
lake build InfoGeometry.Canonical.RelativeModularCommutingLift
```

Umbrella check:

```bash
lake build InfoGeometry.Canonical.All
```

## Method Law

If a claim cannot be attached to an owner theorem in the files above, keep it as hypothesis/interface text only.
