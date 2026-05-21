# BosonizationBoundary

Lean module:

`InfoGeometry.Canonical.BosonizationBoundary`

## Scope

This module formalizes a conservative bosonization boundary for the finite
Tomita/Krein atom.

It packages:

- the zero-mode seed `ε₀`,
- the fact that the zero-mode seed has no Heisenberg anomaly,
- an abstract interface for a genuine current-algebra datum.

## What is proved

The module records the zero-mode boundary of the finite seed:

- `J⁽⁰⁾ₙ = εₙ`
- `J⁽⁰⁾₀ = ε`
- `J⁽⁰⁾ₙ = 0` for `n ≠ 0`
- `[J⁽⁰⁾ₘ, J⁽⁰⁾ₙ] = 0`
- `[J⁽⁰⁾ₙ, ε] = 0`

It also introduces an abstract `BosonizationDatum` record with the intended
Heisenberg interface:

- `current : ℤ → FockEndomorphism E`
- `central : FockEndomorphism E`
- `CCRBracket (current m) (current n) = if m + n = 0 then (m : ℝ) • central else 0`
- `CCRBracket (current n) central = 0`

## Boundary

This module does **not** construct a genuine Heisenberg current algebra from the
finite split atom.

It does not prove:

- mode-sum bosonization,
- normal ordering,
- central charge generation,
- Sugawara/Virasoro construction.

Those remain the missing constructive current-algebra layer.
