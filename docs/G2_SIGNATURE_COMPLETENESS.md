# Native quotient signature completeness

The existing `G2CorrectedCosetSignature` proves invariance and enumerates the
native quotient by 189 inverse word representatives with distinct signatures.
The next reusable statement is the converse: equal signatures mean equal
quotient classes. This turns signature comparisons into an exact quotient
criterion for subsequent two-cell transition proofs. It does not itself prove
BN2. Reuse the existing quotient, signature, enumeration and Nodup certificate.

Source search: recursive Lean search for signature/quotient equivalences and
inspection of `G2CorrectedCosetSignature` and its callers. No duplicate signature
carrier is introduced.

## Acceptance

Parent locked compilation and independent QA both passed the audit target
(9027 jobs). Poincare's independent mathematical review passed; Popper's
independent QA accepted the exact three-lemma scope. Each transitive axiom
report contains exactly `propext`, `Classical.choice`, and `Quot.sound`.
No new-source warnings; QA reported 71 dependency-source and two package
warnings. Strict screening found zero traps, and scoped diff checks passed.
Evidence: `/tmp/g2-signature-completeness.log` and
`/tmp/g2-signature-completeness-qa.log`.

Further source tracing found that `G2BruhatResidualEquiv` already supplies the
five-bit residual equivalence and coordinate readback. `G2ResidualSimpleExact`
already proves the corrected reflection's cell has cardinality 128. A future
constructive continuation is a unique normal form for that entire cell using
`Bool × unipotentSubgroup`, via the existing two-coset complement partition.
That continuation and the Weyl-restricted two-cell BN2 law are not proved by
this signature-completeness module.
