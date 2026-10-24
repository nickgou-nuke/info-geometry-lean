# Positive zero-column deformation

Ground-truth contract: for a real `2 × (n+2)` matrix `C` with every strictly
ordered maximal minor positive, append `ε (C_last - C_first)`. For `ε > 0`
the resulting matrix has positive ordered maximal minors. At `ε = 0` it is
the existing `appendZeroColumn₂ C`. Continuity therefore puts that zero-column
extension in the closure, and hence the frontier, of the strictly positive
matrix-chart region.

Owners: `Canonical.PositiveGrassmannianAmplituhedron` defines maximal minors,
the chart, and the zero-column extension; its
`appendZeroColumn₂_not_mem_positiveGrassmannianInterior` proves exclusion.
`Topology.PositiveGrassmannianAmplituhedronTopological` proves that the strict
region is open. Existing consumers include `AmplituhedronTensorTowerColimit`
and `AmplituhedronBeyondHorizonsGrandSynthesis`; their nonnegative-chart
inclusions remain unchanged.

The new last-column minor is ε times the sum of the old minors `(j,last)`
and `(first,j)`. The endpoint cases have one zero summand and one positive
summand. This finite-stage deformation supplies actual closure membership,
not merely nonnegative membership plus failure of strict positivity.

Scope: strictly positive source matrices with at least two columns. No density
claim for arbitrary nonnegative source matrices, no Grassmannian quotient,
canonical-form residue, amplituhedron boundary, or infinite colimit theorem.

Seven new named lemmas implement the contract in
`Topology.PositiveZeroColumnDeformation`. The companion audit checks eight
declaration heads (including the original exclusion) and three concrete
examples using the positive identity matrix with two columns.

Parent locked audit session 50225 exited zero, 8928 jobs. All eight axiom
reports contain exactly `propext`, `Classical.choice`, `Quot.sound`; no warnings
in the new modules. Existing topology-owner and package warnings remain.
Independent semantic review passed; strict screen found zero traps. Independent
final kernel QA session 49681 also exited zero (8928 jobs), confirming all eight
standard-axiom reports, three examples, zero own-source warnings, and clean
scoped diffs. Accepted with the finite-matrix scope stated above. Session-local
logs: `/tmp/positive-zero-deform-audit.log`, `/tmp/positive-zero-deform-qa.log`.
