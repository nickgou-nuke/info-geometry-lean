# LeanTrail Vacuum Surgery v1.2 Implementation Notes

This bundle supplies the first implementation slice for the v1.2 contract:

1. `lean/InfoGeometry/Lint/NonTriviality.lean`
   Drop-in replacement for the old shallow linter. It preserves the legacy
   `auditExprTriviality : Expr -> MetaM Bool` wrapper, while adding detailed
   expression-shape audit, Prop guard, transitive `collectAxioms` audit, and
   opaque-boundary scanning.

2. `tools/leantrail/vacuity_ingest.py`
   Deep-merges `artifacts/leantrail/vacuity_audit.jsonl` into a LeanTrail
   snapshot under existing flexible `attrs` fields.

3. `tools/leantrail/surgery_plan.py`
   Reads a vacuity-enriched snapshot and emits v1 contraction packets plus
   bridge/alignment candidates. Deletion is intentionally disabled in this
   first implementation slice.

4. `tools/leantrail/surgery_apply.py`
   Applies certified contraction packets using raw binary byte splicing,
   reverse-byte order inside each file, file hash validation, and `lake env lean`
   local checks.

5. `patches/DAG_allowOpaque.patch`
   Required correctness patch for theorem-proof-body visibility in DAG edge and
   fingerprint extraction.

6. `patches/lakefile_v12_scripts.snippet.lean`
   Lake script wrappers for the new Python tools.

Known boundary:

The Lean replacement reports `source_patch` as unsupported unless a separate
InfoTree/body-span extractor supplies `decl_span_kind`, `patch_span_kind`,
`source_info_kind`, byte offsets, and file hash. This is intentional: kernel
`Expr` values must not be used to infer source byte ranges.
