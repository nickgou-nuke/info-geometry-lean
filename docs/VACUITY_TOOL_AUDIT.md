# Vacuity tooling audit and repair record

Date: 2026-10-13

## Scope and authority

Source review preceded execution of the repaired scanners and their relevant dependencies.
The inventory includes all discovered relevant entrypoints, executed lanes, failed lanes,
and outstanding inputs in `reports/vacuity/2026-10-13/script-coverage.json`.
No heuristic report is a proof of mathematical nonvacuity. Owner statements and Lean
kernel evidence remain authoritative.

## Repairs integrated

| Surface | Repair |
| --- | --- |
| LeanTrail compiler biopsy and shared build lock | Compiler precheck; inherited lock descriptor; isolated process group; wait for descendants; observation timeout never kills compilation; disk-backed output; bounded inputs; strict target/schema validation; atomic reports; execution status separated from semantic clearance. |
| Lean NonTriviality screening | Strict no-sorry default; transitive dependency screening before proof-shape scoring; project locality includes owning modules; external gate restricted to Mathlib owners. |
| Source and semantic scanners | Expanded maintained-source roots; selected/read/failure accounting; preserved source coordinates; full declaration spans; explicit lexical provenance; stale or missing source classified unknown. |
| Arango and structural tools | Shared paginated AQL client; malformed results and warnings fail; canonical credential configuration; parameter bindings; missing inputs fail rather than returning a false clean verdict. |
| Critic and significance tools | Dry-run prevents provider and storage mutations; default graph loading is read-only; advisory signals cannot produce policy clearance. |
| Policy and artifact readers | Reject empty, malformed or advisory clearance inputs; strict JSONL parsing; exact input hashes; metadata fingerprints and upstream verification labelled honestly. |

Relevant source paths include `tools/leantrail/vacuity_audit.py`,
`lean/InfoGeometry/Lint/NonTriviality.lean`, `tools/quality/semantic_vacuity_gate.py`,
`tools/quality/semantic_content_audit.py`, `tools/quality/audit_constructivity.py`,
`tools/leantrail/ast_extract.py`, `tools/leantrail/ast_aql_clique_analysis.py`,
`src/igf/graph/arango_http.py`, `src/igf/common/json_io.py`, and the structural,
critic, significance, policy and fingerprint consumers identified in the inventory.

## Observed verification

- Sequential regression suite: **47 passed in 15.88 seconds**. Compiler, provider and
  database failure cases are mocked; these tests do not establish live database coverage.
- Locked build of `InfoGeometry.Lint.NonTriviality`: **3,093 jobs, exit 0**.
- One supervised live biopsy of
  `InfoGeometry.Lie.GenericSplitOrthogonalBlocks.cartanThetaBlocks_preserves`:
  **one selected declaration, one published row, zero execution failures**.
- Live biopsy returned exit **1**, `execution_ok: true`, `status: review_required`,
  `semantic_clearance: false`, because dependency inspection encountered opaque
  boundaries in Mathlib Real wrappers and `String.Internal.append`.
  The row reports no sorry and no vacuous sockets. Opaque-boundary classification
  is an inspection limitation, not a demonstrated mathematical defect.
- Compiler precheck after the probe found no active Lake/Lean process.
- `git diff --check`: exit 0.

Durable evidence: `artifacts/qms/vacuity-tools-2026-10-13/`.
The live probe confirms normal execution and parser transport. Timeout survival and
parent-death lock inheritance were regression-tested with mocks, not forced against
a live compiler.

## Remaining coverage limits

The prior large historical biopsy terminated with exit 137 and supplies no completed
coverage evidence. June/v4.28 expression snapshots cannot certify the present tree.
Missing structural-fiber, representation-depth and Python AST collections remain
explicit prerequisites. Current full compiler expression coverage and owner-level
semantic dispositions remain open. A subsequent locked full default build after the Lean screening and CKM quartet
repairs completed successfully: 33,956 jobs, exit 0. Replayed deprecation and
linter warnings remain; this was not a warning-free build.

Provider senders, graph ingesters, surgery tools and generated-axiom bridges are not
nonvacuity validators and are not automatic source-repair authority. Full vacuity
closure requires substantive mathematical repairs and independent owner review.
