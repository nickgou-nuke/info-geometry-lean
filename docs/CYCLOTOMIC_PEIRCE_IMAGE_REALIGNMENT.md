# Cyclotomic Peirce image realignment

## Ground-truth contract

Candidate: `InfoGeometry.Algebra.CyclotomicPeirceMatrix.ambient_unit_obstruction`.
Its hypothesis is `F.projector i ≠ 1`; conclusion: `blocks F 1 ≠ 1` in the
full ambient matrix ring. It is a conditional boundary, not a universal failure
of matrix representation.

Inspected owners:
- `Algebra/CyclotomicPeirceMatrix.lean`: `blocks F X i j = Pi * X * Pj`,
  `sum_blocks`, `blocks_supported`, `blocks_mul`, `blocks_injective`, `blocks_one`.
- `Core/FinitePeirceMatrix.lean`: native `CompleteOrthogonalIdempotents`,
  `cornerSpace`, two-sided `assemble_blocks` / `blocks_assemble`,
  `cornerEquiv`, multiplication closure, and corner units `Matrix.diagonal e`.
- `Canonical/CyclotomicProjectorReadout.lean`: the same Fourier readout gives
  idempotency, orthogonality, and completeness. Its eigenvalue fields are not
  needed for corner reconstruction.

Positive alternative: for precisely that F, a matrix B has a unique preimage
under `blocks F` if and only if every entry satisfies Pi * Bij * Pj = Bij.
This makes the correct target explicit using the existing native corner space.
The proof must reuse `blocks_assemble`, not reproduce its double-sum proof.
No unrestricted-matrix surjectivity, ambient unitality, spectral existence,
primitive-projector condition, or nonassociative multiplication is claimed.

Search: inspected implementation and consumers of both Peirce owners and
searched `blocks`, `cornerEquiv`, `blocks_assemble`, and supported-image terms
through `lean/InfoGeometry`. This records the selected family's resolution;
it is not a claim that all inventory rows are resolved.

## Verified scope (2026-10-24)

The native specialization is `Algebra.CyclotomicPeirceImage`. Its audit target
compiled in the parent and independent QA runs (9354 jobs, terminal exit 0).
All five audited declarations use only `propext`, `Classical.choice`, and
`Quot.sound`. There are no own-source warnings; dependency warnings remain.
Independent semantic review and scoped acceptance passed; strict screening
reported zero traps. Source hashes and exact session evidence are recorded in
`CYCLOTOMIC_PEIRCE_IMAGE_REVIEW.json`.

The unrelated full staged-source gate ended with failure, including pre-existing
header/static-screen findings and a changed index during its scan. This scoped
verification is not a certification of all staged work.
