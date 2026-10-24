# Counterexample inventory status

The active objective remains repository-wide discovery, semantic review, and
constructive mathematical replacement of counterexamples. No completion claim
is supported by the present lexical inventory or by individual passing builds.

## Completed traversal evidence (2026-10-23)

The long-running inventory command completed with exit code 0. Its JSON result
was inspected after termination, not inferred from a running process or plan.
The result is a navigation artifact, not a Lean parser or semantic audit.

- Result path: `/tmp/counterexample-inventory-v2.json` (ephemeral, not committed).
- SHA-256: `91d7354afe6c8cbf64e0aa563e75f87be7196438e684932c07823f41b18abe2c`.
- Physical Lean files recorded: 479,009.
- Lexical candidate rows: 340,316.
- Read/decode errors recorded: 0.
- Recorded provenance `dependency-or-build`: 151,826 files.
- Recorded provenance `external-ref`: 255,701 files.
- Recorded provenance `generated-artifact`: 9,434 files.
- Recorded provenance `other-review-required`: 8,753 files.
- Recorded provenance `repo-owned`: 50,765 files.
- Recorded provenance `runtime-state`: 2,530 files.

Exclusions reported: symlink: 4,692, git-metadata: 254.

This run included hidden/ignored physical folders, dependency/build trees,
and external references. Symlinks were not followed and Git metadata was
excluded. Copies, historical trees, and dependency sources are separate
records; the file total is not a count of unique maintained theorem owners.
The scanner source-at-launch hash was not recorded, so the result is not a
reproducible immutable source snapshot. Concurrent edits mean recorded file
hashes must be compared against current owners before each review.

## Limits and next work

Negative hypotheses can produce false positives. Indirect counterexamples,
unnamed declarations, and declarations without negative lexical markers can
be missed. Binder defaults can truncate the lexical header scan. Therefore
this traversal does not establish that every counterexample has been found.
The maintained all-folder entrypoint is
`tools/quality/counterexample_inventory_all_folders.py`.

Each selected candidate still requires reading the actual definition, theorem,
imports, and consumers. Record an existing positive replacement when one is
already proved; do not duplicate it. Otherwise formulate a carrier-preserving
canonical alternative, prove it, and run independent review and locked checks.

Recent completed replacements have separate source-backed records:
`BOUNDARY_FIBONACCI_SYLVESTER_REALIGNMENT.md`,
`REFLECTION_ZERO_COUNT_REALIGNMENT.md`, `BINARY_CHART_CURVATURE_REALIGNMENT.md`,
and `CAUSAL_BALANCE_REALIGNMENT.md`. These are local results, not evidence that
the remaining candidate rows have been classified or discharged.

Further source-backed local replacements (2026-10-24):

- `CUNTZ_POSITIVE_GNS_CONTRACT.md`: the positive functional on the corrected
  conjugate-star carrier yields a GNS state, a native complex radical pairing,
  and compatible quotient actions. This does not provide positivity for the
  legacy scalar-fixing complex involution.
- `ZORN_OPERATOR_DEFECT_CONTRACT.md`: left multiplication has an exact
  associator defect, replacing the false general multiplicativity claim.
- `ZORN_TERNARY_DERIVATION_REALIGNMENT.md`: the existing standard-derivation
  bracket satisfies the ternary derivation identity. The raw associator's
  Filippov obstruction remains valid; no total alternation is claimed for
  the corrected operation.

These records reuse inspected owners and have scoped kernel and independent
verification evidence. They do not classify the other inventory rows.
