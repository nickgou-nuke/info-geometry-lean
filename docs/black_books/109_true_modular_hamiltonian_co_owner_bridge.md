# True Modular Hamiltonian as a Co-Owner Bridge

## Status

- Lane: Canonical co-owner bridge
- Scope: explicit modular-Hamiltonian and modular-automorphism translation into doubled/Krein/Hestenes language
- Guardrail: theorem equalities through `Δ`, not replacement definitions

## Core correction

The repo target is not a metaphorical bridge and not a capstone wrapper.
It is an isomorphic co-owner translation:

- keep the owner meaning `K = -log Δ`,
- express the same object in doubled real carrier form,
- prove equalities in the same operator lane.

## Anti-fake-closure rule

Do not introduce a new primitive Hamiltonian by definition.

Wrong pattern:

- `def K_doubled := ...`

Correct pattern:

- prove equalities that route through the owner `Δ` package,
- keep `log` semantics via `exp` witness,
- rewrite generator and flow in `J, ε, J∘ε` form.

## Implemented theorem surface

`lean/InfoGeometry/Canonical/ModularHamiltonianDoubledBridge.lean` records:

- `Δ = exp(δ)` and the equivalent `exp(δ) = Δ`,
- `K := -δ` with certificate `exp(-K) = Δ` (repo-native `K = -log Δ` form),
- true modular generator rewrite
  `A = δ ∘ (J ∘ ε) = δ ∘ J ∘ ε`,
- modular automorphism flow as explicit conjugation by
  `exp(t • A)`,
- closure hook to projected-even super-Hamiltonian identification.

## Architectural consequence

This is the first explicit owner-grade step where the true modular Hamiltonian
is presented directly in doubled/Krein/Hestenes form while preserving its
Tomita meaning.

Thermo and anomaly lanes remain downstream readout shadows.
