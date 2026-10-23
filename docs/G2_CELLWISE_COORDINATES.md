# Native cellwise quotient-table coordinates

For each existing table fiber `orbitCells k`, construct the equivalence
`orbitCells k × U ≃ C((orbitWeylRepresentative k)⁻¹)` with forward value
`(correctedQuotientRepresentative i)⁻¹ * u`. Quotient injectivity recovers i;
group cancellation recovers u. Coverage plus disjointness identifies the correct
table fiber for every element of the cell. This adds cell-label preservation
missing from the bare Fin189 carrier equivalence.

Use finite table cardinalities and corrected native word length to obtain
cell cardinalities, transporting inverse cells by group inversion. Existing
owners read: corrected coset enumeration, corrected Bruhat cover, signature
cell separation, flag partition and corrected word length. No ordered-root
product or inversion-root residual parametrization is claimed.

## Acceptance

Parent locked compilation and independent QA passed (9086 jobs). Poincare's
independent mathematical review passed; Popper accepted the eight-declaration
scope after a separate audit rerun. The transitive axiom union is exactly
`propext`, `Classical.choice`, and `Quot.sound`; `fiber_card_length` uses only
`propext` and `Quot.sound`. Strict screening found zero traps and scoped diffs
passed. QA reported zero own-source warnings, 77 dependency-source warnings,
and two package warnings.
Evidence: `/tmp/g2-cellwise-coordinates.log` and
`/tmp/g2-cellwise-coordinates-qa.log`.

The resulting native Weyl-cell cardinality is `64 * 2^correctedLength p`.
This acceptance covers the explicit cellwise map and cardinality theorem,
not repository-wide closure or an ordered-root coordinate interpretation.
