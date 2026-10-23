# Corrected G2 coset enumeration: theorem contract

The legacy quotient map has a source-proved collision at indices 24 and 45
(`G2QuotientCollisionAudit`). Its injectivity is not an open proof target.
`G2CorrectedQuotientCertificate` supplies 189 corrected words and their group
evaluations, but proves only word-table injectivity. Neither word inequality
nor group-element inequality implies coset inequality.

Carrier: `SplitOctF2Aut ⧸ G2TwoPCSubgroupClosure.unipotentSubgroup`.
The group multiplication applies the left automorphism before the right.
Consequently the flag signature for a right-subgroup coset uses the inverse
automorphism applied to `basis8 4` and the unordered pair
`{basis8 5, add (basis8 4) (basis8 5)}`.

Existing `G2NativeFlagLineCoordinateConstraints` proves that a stabilizer
element fixes the fourth basis image and preserves this pair.
`G2NativeFlagResidualClosure` now proves stabilizer equality and quotient
cardinality 189, with standard axioms only. These facts permit transport of
coset equality to equality of signatures. The implemented finite leaf is
injectivity of `cosetSignature ((correctedQuotientRepresentative i)⁻¹)`;
`correctedCoset` enumerates classes of these inverse evaluations.
Owner build and transitive axiom verification are required for acceptance.

No new matrix model, surrogate group, external count, or injectivity assumption
is introduced. A finite decision proof must run in the kernel. A failed table
check calls for convention/table realignment, not an inconsistent hypothesis.
Even successful coset enumeration will not establish corrected row-to-Bruhat-
cell membership or disjoint double-coset classification by itself.

## Orientation correction

The kernel rejected signature uniqueness for the direct evaluations. The same
finite check passed for inverse evaluations. The maintained map therefore sends
`i` to the coset of `(correctedQuotientRepresentative i)⁻¹`.
GAP's matrix cosets have form `M B`; the native matrix map reverses
multiplication, sending native `gU` to `B A(g)`. Inverting the exported
representatives supplies the required orientation. The exporter already reverses
word order; no further word reversal is introduced.

The owner proves signature invariance under right multiplication by the subgroup,
then transports quotient equality to signature equality. Kernel finite signature
separation proves injectivity. The independently proved quotient cardinality
gives bijectivity and an actual `Fin 189` equivalence. No legacy collision theorem
is used as a premise. Corrected Bruhat-cell witnesses must be transported by
inverting and swapping the left/right factors separately.

## Acceptance

Parent locked owner/audit build and independent QA locked audit rerun passed.
All eight axiom reports individually contain exactly `propext`,
`Classical.choice`, `Quot.sound`. Independent semantic review passed; QA
accepted this quotient-enumeration scope only (9026 jobs, zero own-source
warnings, 73 existing dependency/package warnings). Strict screening found
zero traps. Bruhat-cell membership and double-coset classification remain open.
