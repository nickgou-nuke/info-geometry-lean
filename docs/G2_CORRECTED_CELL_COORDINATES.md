# Corrected reflection cell coordinates

Construct an actual equivalence `Bool × unipotentSubgroup ≃
concreteBruhatCell correctedT`, with value `(if b then r else 1) * correctedT * u`,
where `r = pcWord correctedTRankOneExponent`. Reuse the existing native carrier.
The complement partition supplies surjectivity by moving a complement factor
across the reflection. The already proved cell cardinality 128 and subgroup
cardinality 64 then give bijectivity via mathlib's finite-cardinality theorem.
Expose the value formula and unique normal forms. No BN2 assumption is added.

Read owners: `G2CorrectedTComplementPartition`,
`G2ConcreteBN2CorrectSecondConjugation`, `G2ResidualSimpleExact`,
`G2TwoPCSubgroupClosure`, and `G2TwoBruhatClassification`.
Recursive Lean searches for correctedT equivalences and unique coordinates
found the complement-coset equivalence, not an equivalence for the full cell.
Parent locked compilation and independent QA passed (9007 jobs each).
Independent mathematical review by Poincare passed; Popper accepted the
five-declaration scope after rerunning the audit. Each transitive axiom report
contains exactly `propext`, `Classical.choice`, and `Quot.sound`.
QA found zero own-source warnings, 48 dependency-source warnings, two package
warnings, zero strict-screening traps, and clean scoped diff checks.
Logs: `/tmp/g2-corrected-cell-coordinates.log` and
`/tmp/g2-corrected-cell-coordinates-qa.log`.

This equivalence covers the full corrected-reflection cell, not all cells or
the two-cell BN2 transition. No associative or Lie structure is inferred from
the original nonassociative split-octonion multiplication.
