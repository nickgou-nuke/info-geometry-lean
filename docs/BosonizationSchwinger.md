# BosonizationSchwinger

Lean module:

`InfoGeometry.Canonical.BosonizationSchwinger`

## Scope

This module formalizes the Schwinger boundary of the current algebra story.

It proves the signed crossing-number identity

`signedCrossingNumber m = m`

and packages the abstract interface for a mode-indexed bosonization datum whose
current bracket has Heisenberg form.

## What is proved

The module defines:

- `positiveCrossingNumber`
- `negativeCrossingNumber`
- `signedCrossingNumber`
- `schwingerCocycle`

It proves:

- `signedCrossingNumber m = m`
- `schwingerCocycle m n = if m + n = 0 then m else 0`

It also introduces an abstract `NormalOrderedFermionCurrent` structure with
the target Heisenberg law:

- `CCRBracket (current m) (current n) = if m + n = 0 then (m : ℝ) • central else 0`
- `CCRBracket (current n) central = 0`

## Boundary

This module does **not** construct a normal-ordered current from CAR modes.
It does not prove the Wick contraction or mode-sum bosonization formula.

The constructive source-side theorem still needed is:

- split-Clifford completion
- mode labels
- normal ordering
- current commutator computation

Only then does the existing Heisenberg/Sugawara/Virasoro corridor become a
fully sourced derivation rather than a target surface.
