# Finite GNS quotient reconstruction: theorem contract

Negative owner: `External/Auto/GNSQuotientFinite.lean` proves
`gnsClass nullExample = gnsClass 0` and `nullExample ≠ 0` on native M₂(ℂ).
These concern the class map, not injectivity of `representation`.

Constructive replacement: use the actual `gnsSetoid` and `GNSSpace` to build
`firstColumnEquiv : GNSSpace ≃ V2C`, with inverse the existing
`FiniteGNSConstruction.firstColumnMatrix` followed by `gnsClass`.
Prove it intertwines the actual quotient representation with the existing
matrix-vector action and preserves the defined complex pairing. Recover
matrix entries by applying the action to the two column vectors, hence prove
`representation A = representation B ↔ A = B`.

This identifies the given finite set quotient and pairing; it adds no
infinite-dimensional GNS or continuum claim. No replacement of the carrier,
state, quotient relation, or representation is allowed.
Relevant source search: `GNSQuotientFinite`, `gnsClass`, `firstColumnEquiv`,
`representation_eq_iff`; the finite owner and FiniteGNSConstruction were
inspected. FilteredGNSMatrixFaithfulness is a separate colimit-stage result.

## Verification accepted with limited scope

Parent combined audit session 32686 passed (3,198 jobs, exit 0).
Independent kernel QA session 25438 also passed (3,198 jobs, exit 0),
recorded in `/tmp/mp-gns-final-qa.log`. Across the two batches, all eleven
axiom reports, six examples, and both noncommuting witnesses passed.
The self-adjointness iff uses `propext, Quot.sound`; the metric-equality iff
uses no axioms; the other nine reports use only the standard three axioms.
There were zero own-module warnings, 33 dependency warnings, and two package
notices. Semantic review passed, strict screening found zero traps, and
scoped diffs were clean. This acceptance covers the stated finite/algebraic
contracts only.
