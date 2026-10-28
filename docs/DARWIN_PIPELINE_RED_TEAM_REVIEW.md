# Darwin / InfoTree Pipeline: Socratic Red-Team Review

**Prepared:** 2026-10-28
**Scope:** repository-owned commit, declaration DAG, compiler InfoTree, ArangoDB,
and analysis paths.
**Companion design:** [`DARWIN_PIPELINE_BLUEPRINT.md`](DARWIN_PIPELINE_BLUEPRINT.md)

This review treats graph outputs as navigation and provenance evidence. The
“species / DNA” language is a visualization metaphor: commit ancestry,
declaration digests, InfoTree structure, and similarity do not establish
theorem equivalence or biological ancestry.

## Pipeline map

| Layer | Producer and stored form | What the records mean | Main boundary |
|---|---|---|---|
| `decls` / `edges` | `lean/DAG/Indexer.lean` streamed by `tools/infra/refresh_decl_graph.py`. Legacy writes replace base collections; `--generation-id` writes `decls_g_ID` / `edges_g_ID` and a `decl_graph_generations` record. | Compiler-indexed declarations and reference edges. A generation fingerprint is caller supplied; it is not independently verified source provenance. | Import errors and generation publication must be checked before a generation is advertised. |
| `raw_info_nodes` / `raw_info_edges` | `tools/infra/materialize_lossless_infotree.py` reads `decls.jsonl` and `raw_edges.jsonl`, writes a declaration dependency DAG plus additive SCC/topology overlays. | “Raw” here means the unfiltered declaration DAG input to this materializer. Its losslessness claim is relative to that input; this is not the compiler `RawInfoTreeExport` lane. | Do not interpret these rows as InfoTree nodes or use an SCC quotient as a replacement for raw edges. |
| `raw_infotree_*` | `lean/DAG/RawInfoTreeExport.lean` exports a per-file compiler InfoTree forest, node/payload/context/declaration-link rows, tactic and goal observations, and projection-leakage rows. `tools/infra/batch_raw_infotree_export.py` validates files and merges successful exports. | Elaboration observations from a particular Lean run. Export metadata explicitly says `fully_lossless=false` and `loss_audited=true`; the validator separates structural validity from `lossless_ok`. | `batch_report.json` records selected, successful, failed, and timed-out files, but the Arango importer consumes the merged directory and does not carry that report into the generation record. |
| `raw_infotree_generations` | `tools/infra/arango_raw_infotree_ingest.py` writes generation-suffixed collections, imports rows and edges, counts them, then inserts a registry document with `status: complete`. | Current `complete` means the final registry write was reached. It does not certify intended-source coverage, full losslessness, independently checked build provenance, or feature eligibility. | A crash before the registry write can strand collections; the same content/fingerprint derives the same 24-hex generation ID and existing collections block retry. |
| `commit_*` | `tools/infra/darwin_commit_graph.py` imports Git commit nodes, parent edges, heuristic taxonomy ranks, and optionally commit-to-declaration edges. | Git ancestry and descriptive change labels. Optional declaration edges parse added declaration-looking lines but resolve names against current `decls`, not a historical declaration census. | The writer previously used generic Arango database settings while the visualizer defaulted to `darwin_commits`; this review adds a shared Darwin-role resolver. |
| `evo_*` | `tools/infra/evolution_extract.py`, taxonomy/path-habitat tools, and `tools/infra/evolution_ingest.py`. Collections are `evo_commits`, `evo_labels`, `evo_parent_edges`, `evo_files`, `evo_commit_files`, and `evo_file_numstats`. | Streaming commit/path/numstat history with rule-based labels and path-derived habitats. Labels are weak classifications, not calibrated probabilities. `--replace` truncates only these six collections. | Keep this offline/extracted history distinct from `commit_*`; do not silently merge their schemas or imply that path cohabitation proves an exact declaration edit. |
| `ig_nodes` / `ig_edges` | LeanTrail and other compact graph projections. `tools/infra/arango_causal_memory.py local-attention` instead reads local `artifacts/dag/index`; its Arango preflight explicitly requires `--use-projection-cache`. | A retrieval projection, potentially stale or lossy. It is not the raw InfoTree source. | An analysis must identify its exact projection and derivation. “Old” alone does not invalidate a projection; unbound or insufficient inputs do. |

The commit and evolution sources are DAGs when merges are present. Offline
`phylogeny_export.py` preserves ancestry and checks that compressed display
chains expand to the original parent-edge multiset. `dna_character_tree.py`
uses exact qualified names and compatible closed digest markers to construct
an **unrooted structural-affinity** tree; it does not infer historical ancestry,
renames, theorem equivalence, or a molecular clock. `ancestry_hodge.py` computes
integer incidence/cycle certificates for the Git graph as a 1-complex. These
are separate views over distinct evidence.

## Findings confirmed in owner code

1. **Database routing mismatch:** `darwin_commit_graph.py` previously called
   generic `arango_database()`; `darwin_tree_visualizer.py` defaulted the commit
   database to `DARWIN_ARANGO_DATABASE` or `darwin_commits`. `evolution_ingest.py`
   also used a Darwin database setting but resolved endpoint and credentials
   separately. This review now centralizes Darwin endpoint/database/user/pass
   resolution in `normalized_darwin_arango_env()` and uses it in the writer,
   visualizer, and evolution importer. Explicit CLI database overrides remain.
2. **False completion on reported raw-import errors:** `import_rows()` accumulates
   per-collection `created`, `updated`, `errors`, and `total`, while the ingest
   path previously wrote `status: complete` without checking those results.
   A new accounting gate rejects reported errors and any submitted-row count
   not accounted for before registry publication.
3. **Declaration import response ignored:** `refresh_decl_graph.py` previously
   ignored the dictionary returned by `import_bulk`. It now rejects reported
   bulk errors before continuing to endpoint validation and generation
   publication.
4. **Recovery remains incomplete:** both generation writers create collections
   before writing their final generation record. Raw InfoTree ingest explicitly
   refuses reuse when any collection for the same generated ID already exists.
   The declaration writer similarly refuses when a generation collection is
   already present. No automatic deletion or adoption is safe; orphan
   reconciliation remains a follow-up.
5. **Coverage is not carried into Arango:** the batch report knows the selected
   file inventory and per-file outcomes. The ingest preflight records merged
   metadata and source provenance, but does not consume `batch_report.json`.
   Thus a merged, structurally valid subset can be ingested without the registry
   preserving the selected-versus-successful denominator.
6. **Caller fingerprint is a claim:** raw InfoTree generation identity hashes
   the provided build-fingerprint together with eligible export files. The
   fingerprint is not itself checked against the actual Lean build. Since the
   collection suffix is a digest, separator/control characters in the supplied
   label are not directly interpolated into the collection name; test provenance
   conflation, not path injection through that field.
7. **Destructive operations are explicit:** the declaration legacy path
   truncates base collections; raw InfoTree `--drop-existing` drops its target
   collections; `commit_* --drop-existing` truncates commit collections;
   `evo_* --replace` truncates its six owned collections. They are not default
   behaviors. Review invocations and target identity before enabling them.

## Threat model and safe tests

Assets include source-to-record bindings, coverage inventories, generation
contents and publication records, graph topology, private payloads and author
metadata, and bounded local storage/compute. The tested boundaries are source
to exporter, export to validator/importer, environment to database connection,
collections to registry publication, published data to joins/projections, and
analysis inputs to logs/models/GPU.

Every future integration/fault-injection test must use an isolated harness with
synthetic files and fake database/model/GPU clients, no live credentials, no
network route to Arango, and no host database socket. If those boundaries
cannot be enforced, the test is not run. The table distinguishes executed
unit tests from proposed tests.

| Priority / failure mode | Fixture and pass condition | State |
|---|---|---|
| P0: role/configuration drift | Environment-only unit fixture sets generic DB to `infogeometry`; Darwin defaults resolve to `darwin_commits`; Darwin-specific endpoint/user/pass override generic values. | **Run:** `tests/test_arango_env.py` (17 passed). |
| P0: failed Arango batches still marked complete | Fake result maps cover clean accounting, explicit errors, and under-accounted submissions. Any error or mismatch rejects publication. | **Run:** `tests/test_arango_raw_infotree_ingest.py` includes the new accounting gate test; included in 19-pass run. No Arango client is constructed. |
| P0: crash/orphan retry | Fake collection API injects failure before/after each create/import/count/registry step. A failed attempt is never readable as published; retry uses a fresh attempt identity; previous published data remains. | **Proposed, not run.** |
| P0: partial batch promoted to source-complete | Three-file fixture: one valid, one timeout, one validation failure; also test absent inventory. The record preserves expected and successful counts; absent inventory means coverage unknown, not complete. | **Proposed, not run.** Existing batch report records outcomes, but persistence through Arango is not yet implemented. |
| P0: accidental cross-generation join | Two synthetic snapshots share declaration names but differ in source/span/edges; add one unbound projection and one declared comparison pair. Reject silent “latest” mixing; accept only explicitly bound pairs. | **Proposed, not run.** |
| P1: wrong fidelity gate | Synthetic loss records distinguish optional omitted payload, required missing graph edge, and unlocalized loss. Permit a names-only feature only when its row/name footprint is proven intact; reject topology analysis when required edges are missing or relevant loss is unknown. | **Proposed, not run.** Zero global leakage is not a universal gate. |
| P1: malformed JSONL / identity collision | Temporary files contain duplicate JSON keys, duplicate document IDs with conflicting data, bad types, dangling endpoints, oversized lines, and Unicode/undecodable path bytes. Reject or quarantine before publication; preserve supported path identity; do not touch an external sentinel file. | **Proposed, not run.** |
| P0 if external dispatch is enabled: privacy egress | Synthetic canary secret/email through success, validation-error, and exception paths; fake model and log sinks; network disabled. No disallowed canary may leave the local fixture. | **Proposed, not run.** Current external review prompts contained pipeline descriptions, not raw InfoTree payloads or commit author records. |
| P1: stale graph / unsafe compute | Fake projection with mismatched node-index map and missing required edges; resource-budget stubs reject before allocation; no GPU device exposed. | **Proposed, not run.** |
| P2: destructive flags and cleanup | Fake API records all calls. Verify default invocations do not call truncate/drop, and no orphan or low-capacity scenario triggers deletion. | **Proposed, not run.** |

The two external audits were advisory. Google AI Mode returned uncited
recommendations; ChatGPT explicitly said it had not inspected repository files
or run tests, so its claimed “real recovery hole” was independently checked in
the owner scripts above. Neither provider output counts as repository evidence.
Both reviews converged on separate lifecycle, coverage, fidelity, provenance,
and feature-eligibility claims. Their proposal to delete incomplete generations
was rejected: reconcile read-only, then use a fresh attempt ID; retain artifacts.
Their broad zero-leakage rule was narrowed to fidelity over each feature’s
declared dependency footprint.

## Implemented in this review

- Added `normalized_darwin_arango_env()` with a dedicated default database
  (`darwin_commits`) and Darwin-specific overrides, falling back to generic
  endpoint/credentials only.
- Routed `darwin_commit_graph.py`, `darwin_tree_visualizer.py`, and
  `evolution_ingest.py` through the shared resolver.
- Added raw InfoTree import accounting checks before writing a generation as
  complete; added an error check to the declaration DAG bulk importer.
- Added local unit coverage for role isolation and import accounting.

**Verification:**

```text
python -m pytest -q tests/test_arango_env.py tests/test_arango_raw_infotree_ingest.py
19 passed in 0.71s
git diff --cached --check
passed
```

These are local unit tests only. No live Arango database, destructive path,
Lean build, or GPU was used. Remaining work is a non-destructive generation
registry/recovery design, propagation of the batch inventory and localized loss
records, and feature-specific analysis manifests. Graph/model outputs remain
navigation evidence, not proof of theorem semantics.
