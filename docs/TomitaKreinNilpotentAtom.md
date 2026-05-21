# Tomita-Krein Nilpotent Atom

Lean module:

`InfoGeometry.Canonical.TomitaKreinNilpotentAtom`

## Scope

This module formalizes the finite doubled real Krein atom behind the notation
`{1, ε, J, Jε}`.

It proves:

- `J² = 1` for `modular_j`
- `ε² = 1` for `spectral_epsilon`
- `Jε = -εJ`
- `Jε = complex_i`
- `(Jε)² = -1`
- `P₊² = P₊`, `P₋² = P₋`, `P₊P₋ = P₋P₊ = 0`, `P₊ + P₋ = 1`
- the concrete split-null CAR operators satisfy `u₊² = 0`, `u₋² = 0`
- their products recover the idempotents: `u₊u₋ = P₊`, `u₋u₊ = P₋`
- their finite commutator reads out the grading sign: `[u₊, u₋] = ε`

## Boundary

This is not a Heisenberg, Kac-Moody, Sugawara, or Virasoro construction.
Those layers require mode labels, normal ordering, and central extensions.

The module also does not identify `clockAxis` with a Krein involution:
`clockAxis = Jε = complex_i` and squares to `-id`, while the Krein sign
operator `ε` squares to `id`.

The matrix-facing split-quaternion causal-cone closure is owned separately by:

```lean
InfoGeometry.Clifford.SplitQ11CausalCone
```

That module proves the local projector, null-hop, finite squeeze, and
off-diagonal mass-bridge laws.  It is still a finite local theorem surface,
not a global physical necessity theorem.

## Interpretation

The map to the doubled real Krein space is:

```text
(x, ξ) --ε--> (x, -ξ)
(x, ξ) --J--> (ξ, x)
I = Jε
```

The idempotent sectors are the spectral projectors of `ε`:

```text
P₊ = (1 + ε) / 2
P₋ = (1 - ε) / 2
```

The nilpotent split-null operators are the concrete CAR creation and
annihilation operators already owned by `SuperchargeCARCCRBridge`.  The new
module only assembles their proven identities into a single finite theorem
surface.
