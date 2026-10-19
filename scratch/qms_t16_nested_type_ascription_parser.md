# QMS CAPA — T16 nested matrix type-ascription parsing

## Task contract

- **Task ID:** `QMS-T16-NESTED-ASCRIPTION-2026-10-19`.
- **Risk:** R2 (OpenGauss static-screen parser; Lean theorem source is unchanged).
- **Intake:** the valid `matrix_fin2_noncommutative` theorem in
  `lean/InfoGeometry/Algebra/AiStudioNativeMathlibFindings.lean` uses typed
  operands whose type is `Matrix (Fin 2) (Fin 2) R`. The current screener
  strips inline type ascriptions using a flat regex that cannot consume the
  nested parentheses in this carrier, so the T16 matcher does not recognize
  the actual witness.
- **Claim:** teach `_strip_inline_type_ascriptions` to remove only a simple
  parenthesized identifier type ascription using balanced Lean atoms, while
  preserving named arguments and all witness/carrier checks.
- **Acceptance:** the regression witness is accepted by the existing
  noncommutativity parser and T16 screen; existing negative tests for assumed,
  unrelated-carrier, false-elimination, and name-only witnesses continue to
  reject; Python protocol tests pass.
- **Explicit exclusions:** no T16 rule is weakened; no Lean theorem or carrier
  is added/changed by this parser repair; this is not kernel evidence for the
  witness, whose owner module is independently checked by Lean builds. No
  claim is made about every Lean syntax form beyond this balanced simple
  identifier-ascription case.

## Owner search and evidence

- T16 implementation owner: `tools/infra/opengauss_screener.py`,
  `_strip_inline_type_ascriptions`, used by the closed noncommutativity witness
  matcher and carrier comparison.
- Regression-test owner: `tests/test_opengauss_protocols.py`, adjacent to the
  existing T16 closed-witness tests.
- Lean witness owner: `lean/InfoGeometry/Algebra/AiStudioNativeMathlibFindings.lean`,
  theorem `matrix_fin2_noncommutative` on `Matrix (Fin 2) (Fin 2) R` with
  `[Ring R] [Nontrivial R]`.
- This change is a parser CAPA only. QGT scalar-normalization edits are a
  separate source issue and are recorded in `scratch/qms_cl44_chirality_gate0.md`.

## Gate status

- Source patch and regression are staged immediately per repository policy.
- The strict screener passes on `AiStudioNativeMathlibFindings.lean` with zero
  traps; the QGT owner also passes strict screening with zero traps.
- Focused T16 protocol tests: 41 passed, 67 deselected using the Sage Python
  environment's pytest. The default `python3` environment lacks pytest.
- Semantic-vacuity scan: 0 findings on the AI Studio owner. QGT has one
  `trivial_surface` warning on the definitional theorem
  `symmetricPartTwice_is_symmetric` at line 49; independent source review
  classified it as a genuine simple symmetry fact, not a vacuity.
- Corrected-diff A-A passed after the nonempty-type guard was added. The guard
  leaves malformed `(x : )` unchanged; the regression covers this and named
  argument preservation. Carrier matching remains unchanged.
- Independent QA-A passed on the final diff and reran the focused T16 suite
  (41 passed, 67 deselected) plus strict screening (0 traps). Fresh locked owner
  builds and Gate 4 remain pending; no Lean theorem claim is certified by this
  parser CAPA.
- The isolated repository-wide staged proof-proxy hook completed successfully
  (`proof_proxy_staged_gate: ok`). Gate 4 still needs to rerun against the now
  stable staged snapshot and complete its locked owner/audit verification.
