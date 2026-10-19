# QMS theorem contract: ternary coefficient flattening

## Intent and classification

- Task: add a finite coefficient-carrier interface for the existing Shirokov ternary matrix expansion.
- Classification: theorem-bearing, finite-dimensional, risk R3 (new carrier interface and audited module).
- Bucket target: Bucket 2 until the Lean owner and audit compile; then Bucket 1 for the exact finite statements below.

## Exact mathematical claim

For a coefficient array `c : Fin 3 → Fin 3 → ℂ`, and a parameter `ω` satisfying
`ω ^ 2 + ω + 1 = 0`, define its matrix flattening by the repository's existing
nine-term Sylvester expansion. Define the coefficient grade-zero projection by
retaining only `c 0 0`. Then the flattened grade-zero part equals the normalized
matrix trace of the flattened coefficient array times the identity matrix.

This is a coefficient-to-matrix statement. The initial task did not assert
uniqueness or injectivity; a separately reviewed follow-up now proves
injectivity at the canonical root (see
`scratch/qms_qutrit_coeff_contract.md`). The local source names Eq. 7.67
for a different identity (`U + underline U = 2 <U>₀ I`), so this contract uses
the neutral name “normalized-trace identity” and makes no equation-number claim.

## Carriers and conventions

- Matrix carrier: `Matrix (Fin 3) (Fin 3) ℂ`.
- Shift: `ternaryShiftP` from the Shirokov owner.
- Clock: `ternaryClockR ω` from the Shirokov owner.
- Basis order: `(0,0), (1,0), (0,1), (2,0), (0,2), (1,1), (2,1), (1,2), (2,2)`,
  matching `ternaryMultivector`.
- Root hypothesis: `ω ^ 2 + ω + 1 = 0`.
- Grade zero on coefficient arrays means retaining coefficient `(0,0)` only.
- Shirokov's existing `ternaryUnderline` remains the involution
  `2 * ternaryShirokovGrade0 U • 1 - U`; it is not the traceless projection.

## Source-confirmed owners and facts

Owner: `lean/InfoGeometry/Synthesis/ShirokovTernaryCliffordUnitarySU3Synthesis.lean`.

- `ternaryMultivector` is a matrix-valued nine-coefficient expansion.
- `ternaryMultivector_trace_eq` proves its trace is `3 * u00` under the root hypothesis.
- `ternaryShirokovGrade0_multivector` proves normalized grade-zero extraction of `u00`.
- `ternaryShirokovGrade0_mul_comm`, the actual Shirokov underline laws, characteristic
  coefficients, adjugate, determinant relation, inverse, SU(3) closure, and Gell-Mann
  transitions are already present and are not duplicated by this task.
- The companion audit is `ShirokovTernaryCliffordUnitarySU3SynthesisAudit.lean`.

## Smallest gap and acceptance

The owner has no explicit coefficient-array structure, coefficient grade-zero map,
or theorem phrased as flattening that projected array. Add that adapter and prove:

1. Its flattening agrees definitionally/algebraically with the existing
   `ternaryMultivector` expansion.
2. Flattening the coefficient grade-zero projection is the `(0,0)` coefficient
   times the identity.
3. This equals `(1 / 3) * trace(flat c)` times the identity, under the root hypothesis.

Acceptance requires a focused owner module and audit, strict OpenGauss screen, and
serialized locked kernel verification. The initial contract alone does not claim
basis uniqueness or injectivity; the follow-up contract records the separate
linear-independence argument for the nine canonical Weyl monomials.

## Explicitly excluded / corrections

- The user's proposed `A - grade0(A) I` is a traceless-part projection, not the
  repository's Shirokov underline. No theorem about it is labeled as a Shirokov
  Eq. 7.74/7.75 identity.
- With the owner's shift and clock matrices, the established relation is
  `P * R = ω • (R * P)`; the reversed ordering has the inverse phase.
- The original flattening task did not prove uniqueness. The later Weyl-basis
  bridge does prove injectivity for the canonical root and the repository's
  stated opposite-shift reindexing. Neither contract claims an abstract algebra
  isomorphism or a W24 correspondence.
