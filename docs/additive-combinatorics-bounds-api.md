# Additive Combinatorics Bounds API

> Status: `finite shadow`
> Owner: `lean/InfoGeometry/Arithmetic/AdditiveCombinatoricsBounds.lean`

This page records the source-owned additive-combinatorics packet for the prime-boundary lane.

## What is proved

- `sumset` is the explicit finite sumset construction on a commutative additive group.
- `sumset_expansion_bound` packages the finite Cauchy-Davenport-style lower bound as a proposition.
- `MicrostateIntegerBound` records the finite entropy-vs-prime-rank inequality as a structured witness.
- `prime_lattice_combinatorial_bound` proves the sumset cardinality is positive when both inputs are nonempty and the expansion bound is assumed.

## What is not proved

- a general Cauchy-Davenport theorem for arbitrary finite groups
- a continuum entropy theorem for Bekenstein-Hawking black holes
- a derivation of the inequality `S_BH <= prime_rank * log 2` from microscopic state counting

## Practical use

Use this module as the finite combinatorial boundary readout for the prime-lattice lane.
