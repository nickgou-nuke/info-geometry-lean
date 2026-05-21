# ConnesTomitaKreinDerivation

Lean module:

```lean
InfoGeometry.Volume.ConnesTomitaKreinDerivation
```

## Scope

This module is the finite algebraic readout connecting two already-owned
surfaces:

```lean
InfoGeometry.Volume.ConnesInfinitesimal
InfoGeometry.Clifford.SplitQ11Projectors
```

`ConnesInfinitesimal` proves that exponential modular transport has
infinitesimal generator given by a commutator.  This file proves the finite
split-`Cl(1,1)` counterpart: when the modular sign is the local Krein involution
`epsGen`, its commutator is exactly twice the commutator with the positive
spectral projector.

It does not construct a mode-indexed current algebra, normal ordering, a
Schwinger term, Sugawara operators, or Virasoro.

## Main Theorem

The definitions are:

```lean
finiteKreinModularDerivation A =
  epsGen * A - A * epsGen

finiteKreinPositiveProjectorCommutator A =
  epsPlusProjector * A - A * epsPlusProjector
```

The theorem:

```lean
finiteKrein_projector_commutator_as_modular_derivation
```

proves:

```text
[epsGen, A] = 2 [epsPlusProjector, A]
```

using the owner theorem:

```lean
epsPlusProjector_eq_half_one_add_eps
```

That is the finite projector form of the modular commutator readout.

## Finite Exponential Representative

The module also defines:

```lean
finiteKreinIdempotentExponential t =
  exp(t) * epsPlusProjector + exp(-t) * epsMinusProjector
```

and proves:

```lean
finiteKrein_idempotent_exponential_zero
finiteKrein_idempotent_exponential_add
finiteKrein_idempotent_exponential_mul_neg
finiteKrein_idempotent_exponential_neg_mul
finiteKrein_idempotent_transport_zero
```

These are finite idempotent-calculus facts.  They are the local algebraic
analogue of modular exponential conjugation, not an infinite-dimensional
operator-exponential theorem.

## Boundary

Solved here:

```text
finite Connes commutator readout
+ finite Krein projector leakage
+ finite idempotent exponential calculus
```

Still outside this module:

```text
raw CAR modes -> normal-ordered current -> Heisenberg Schwinger term
```

