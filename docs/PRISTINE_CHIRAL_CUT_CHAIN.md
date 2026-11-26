# Pristine chiral-cut reconstruction

This is the source-grounded claim ledger for the recovered chiral-cut
archetype. It records the mathematical correction, not a reconstruction of
private chain-of-thought.

## Input atoms and corrections

The recovered stream mixed four distinct notions:

1. a projector/idempotent (`P * P = P`);
2. square-zero ladder operators (`E_R * E_R = 0`, `E_L * E_L = 0`);
3. a grading/commutator (`E_R * E_L - E_L * E_R = Γ`);
4. an anticommutator normalization (`E_R * E_L + E_L * E_R = 1`).

They are not interchangeable. In particular, an idempotent is not nilpotent,
a chiral grading is not automatically the difference of the two projectors, and
an ordered operator product cannot be replaced by a commuting scalar product.

The repository already contains the canonical finite carrier:

`InfoGeometry.OperatorAlgebra.ChiralRailPlane.ChiralRailPlane`

in both source lanes:

- `lean/InfoGeometry/OperatorAlgebra/ChiralRailPlane.lean`
- `src/InfoGeometry/OperatorAlgebra/ChiralRailPlane.lean`

Its `Ring R` structure fields state the finite matrix relations explicitly and
its `standardChiralRailPlane` supplies the concrete `2 × 2` Mathlib matrices.

## Causal mathematical chain

```text
finite matrix carrier over Ring R
  → nilpotent E_R,E_L and normalized anticommutator
  → chiralSum := E_R + E_L
  → chiralDifference := E_R - E_L
  → chiralSum² = 1 and chiralDifference² = -1
  → ordered products recover ±Γ
```

The final two signs are order-sensitive:

```text
chiralSum * chiralDifference = -Γ
chiralDifference * chiralSum =  Γ.
```

These are genuine ring identities proved by distributivity, the two
square-zero hypotheses, the anticommutator field, the commutator field, and
`abel`; no commutativity or scalar surrogate is introduced.

## Formalization status

`ChiralRailPlane.lean` previously contained eleven proof holes, including an
incorrectly stated `symplectic_anti_compatibility` claim: the structure field
assumes preservation `Kᵀ * Ω * K = Ω`, while the theorem claimed anti-preservation
`Kᵀ * Ω * K = -Ω`. Since no consumer used those declarations, they were removed
rather than promoted as wrappers or false aliases. Their valid algebraic content
is retained by the four substantive chiral-combination theorems above.

The following remain deliberately open unless separately stated and proved:

- identifying `Γ` with a projector difference;
- a continuum spacetime or physical Hamiltonian interpretation;
- a Yang–Mills, BdG mass-gap, or quantum-field reconstruction theorem;
- any psychological or consciousness interpretation of the metaphorical stream.
