# Word readout of the positive quotient product functional

Contract: compute the already constructed `quotientProductFunctional` on
every genuine quotient word pair. The answer is zero for unequal words and
the product of letter weights for equal words. Use the existing coherent
matrix reindexing and `productFunctional_wordMatrixUnit`; unequal lengths
vanish under the existing degree-zero projection.

Owners: `CuntzComplexStarProductPositivity`, `CuntzComplexStarFiniteStageHom`,
`CuntzComplexStarColimitEmbedding`, and `MatrixProductWordReadout`.
No scalar word formula is used to define a purported quotient functional:
the formula is derived from the existing normalized positive linear map.
The binary uniform specialization agrees with `canonicalGaugeState`.
This is required for subsequent multiplication/KMS work, not itself KMS.
The spanning theorem also proves that complex-linear functionals on the
quotient are uniquely determined by these word-pair values.

Verification (2026-10-24): the locked audit target
`InfoGeometry.OperatorAlgebra.CuntzComplexStarProductWordReadoutAudit`
completed successfully (9420 jobs), independently rerun by QA with exit zero.
All four axiom reports contain exactly `propext`, `Classical.choice`, and
`Quot.sound`. The two new Lean files have zero compiler warnings; the build
reports 732 dependency-source warnings and two package notices.
Strict screening detected zero traps. Independent semantic review passed.
QA requested a license header on the audit file; that comment-only correction
was applied after the rerun. Logs: `/tmp/cuntz-word-readout-audit.log` and
`/tmp/cuntz-word-readout-qa.log`.

Readout and uniqueness do not require nonnegative weights. Positivity of the
previously constructed functional requires the separate `∀ i, 0 ≤ q i`
hypothesis. Full algebraic KMS is now proved in a separate owner; see
`CUNTZ_QUOTIENT_ALGEBRAIC_KMS_CONTRACT.md`.
