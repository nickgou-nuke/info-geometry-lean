# QMS Record: Ontology Pipeline Review and QA

- Task ID: `ONTOLOGY-PIPELINE-20261105`
- Checkout HEAD: `ee2dd4ad7d5329980367acbb951f0986a5fe4317`
- Working tree: dirty, with substantial pre-existing staged and unstaged work. QA explicitly tested the dirty checkout; results do not describe HEAD alone.
- Scope: declaration-DAG refresh/resolution and the Arango-to-Auto-Ontology PostgreSQL import path. This is pipeline/QMS evidence, not Lean theorem acceptance.
- Changed by this review: this record only. No pipeline owner, test, or candidate projection source was edited in this review turn.

## Role assignments and dispositions

- G-A: prior pipeline implementation/candidate authorship in the shared checkout; not treated as an audit or acceptance role.
- A-A: independent read-only subagent review of current pipeline owners, tests, docs, and projection candidates. Disposition: **REQUEST_CHANGES**.
- QA-A: separate test-running subagent, distinct from A-A and the author. Disposition: **ACCEPTED_WITH_LIMITED_SCOPE** for the requested mocked/unit-test slice only.
- Projection candidate review: Copernicus returned a separate read-only review of `scratch/ontology_pipeline_candidates/projection/`; the candidate remains **UNRUN / unaccepted** and is not integrated.

## A-A findings and CAPA

1. **Critical: the `--generation-id` flow is not a generation-scoped PostgreSQL projection.** The term and relationship importers write shared legacy tables; no immutable generation membership, selected snapshot, historical removal, or request-pinned API read is established. CAPA: implement and integrate generation-owned snapshots and pinned consumers before claiming PostgreSQL generation scope.
2. **High: importer batches can partially commit.** Later count/reconciliation or source failures do not roll back earlier committed batches. CAPA: stage complete data, validate, then atomically publish; test injected failure at publication and assert selected reads remain unchanged.
3. **High: source identity is not isolated.** Terms use shared `semantic` source and `(name, source)` upsert; relationship ID resolution is global. CAPA: integrate a collision-safe deployment/database identity into persisted writes and lookups; verify in a disposable PostgreSQL integration test.
4. **High: source receipt does not establish immutable, complete content.** Resolver checks metadata/counts/collection presence and endpoint validity but does not validate every stored declaration/edge identity or content digest. Extraction is not demonstrably stable across reads and receipt counts can be replaced by collection recounts. CAPA: validate identities and content against a source-derived commitment, preserve receipt expectations, and enforce/document completed-generation write protection and exporter/build provenance.
5. **Medium: zero-edge complete generations are rejected by the relationship importer.** CAPA: accept receipt-validated zero-edge generations while retaining malformed/empty legacy-input guards.
6. **Medium: runtime DDL does not verify schema compatibility or least privilege.** CAPA: use a reviewed migration/version check and test install, re-install, drift, and writer/reader permissions.
7. **Documentation wording must distinguish generation-selected input from generation-scoped persistence.** CAPA: retain additive-legacy-import language until the snapshot store and consumers are integrated.

The current pipeline changes do contain useful safeguards (strict source IDs, record/count checks, endpoint preflight, explicit returned-term mapping checks, keyword credential transport, and child-process cleanup). These do not close the CAPA items above. The isolated v2 term-source helper is unintegrated and its candidate tests import owner modules that do not exist in the checkout.

## QA-A commands and result

Before execution, QA-A observed no matching active Lean/Lake/test processes. Tests ran sequentially from the checkout root with these exact commands:

```bash
ONTOLOGY_LIVE_TEST=0 PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=.:src python3 -m unittest discover -s tests -p 'test_decl_graph_generation.py' -v
ONTOLOGY_LIVE_TEST=0 PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=.:src python3 -m unittest discover -s tests -p 'test_refresh_decl_graph_executable.py' -v
ONTOLOGY_LIVE_TEST=0 PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=.:src python3 -m unittest discover -s tests -p 'test_decl_graph_receipt_integrity.py' -v
ONTOLOGY_LIVE_TEST=0 PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=.:src python3 -m unittest discover -s tests -p 'test_ontology_relationship_identity.py' -v
ONTOLOGY_LIVE_TEST=0 PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=.:src python3 -m unittest discover -s tests -p 'test_ontology_term_integrity.py' -v
ONTOLOGY_LIVE_TEST=0 PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=.:src python3 -m unittest discover -s tests -p 'test_pipeline_publication_adversarial.py' -v
ONTOLOGY_LIVE_TEST=0 PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=.:src python3 -m unittest discover -s tests -p 'test_astaql_concept_bridge.py' -v
```

| Test file | Passed | Skipped | Exit |
|---|---:|---:|---:|
| `test_decl_graph_generation.py` | 6 | 0 | 0 |
| `test_refresh_decl_graph_executable.py` | 2 | 0 | 0 |
| `test_decl_graph_receipt_integrity.py` | 16 | 0 | 0 |
| `test_ontology_relationship_identity.py` | 7 | 0 | 0 |
| `test_ontology_term_integrity.py` | 3 | 0 | 0 |
| `test_pipeline_publication_adversarial.py` | 14 | 1 | 0 |
| `test_astaql_concept_bridge.py` | 5 | 0 | 0 |
| **Total** | **53** | **1** | **0** |

The skipped test was `LivePreflightTests.test_edge_validation_predicate_with_bound_fixtures`, requiring configured Arango; `ONTOLOGY_LIVE_TEST=0` excluded live execution. QA-A reports that SHA-256 checks for the seven test files and six pipeline owners matched before and after the run. No candidate-v2 test was run because its proposed import modules are absent. No database, migration, service, or production write was performed.

## Scope limits and final status

QA-A acceptance is limited to mocked/unit behavior in the dirty checkout. It does not establish live AQL behavior, current graph freshness, PostgreSQL transaction/trigger/locking behavior, concurrent publication or pinned reads, historical membership/removals, REST/MCP integration, real source completeness/stability, or exporter artifact provenance.

**Overall disposition: OPEN / NOT ACCEPTED.** The pipeline source audit requests changes, while the narrow unit-test slice passes. CAPA remains open; the PostgreSQL generation-store candidate is not approved for integration or production use.

## Source fingerprints recorded during review

These are working-tree fingerprints observed during this review, not signatures or immutable records:

| File | SHA-256 |
|---|---|
| `tools/infra/refresh_decl_graph.py` | `722000300e7113bbd896714765b82bb13a8add57b64cf5c162c467ce8d21f4ec` |
| `tools/infra/decl_graph_generation.py` | `9f4543b2409c0b0b85be6391560df027ac6aa685f00f733174e74631cc7d9517` |
| `tools/infra/arango_to_ontology.py` | `ad730a1eb0c39fe07ea470ad2ad3b07e9960746d04e479473eb2e332b5616e16` |
| `tools/infra/arango_to_ontology_relationships.py` | `4bd7ae26af32b77df4892d6f59c03573c94da0086ef4fe36757df8541eb3ff7a` |
| `scratch/ontology_pipeline_candidates/projection/generation_store.py` | `70d3d4a62d20321a1fa35eac695b6ee833757ff9b3668bc095c98b0366adb3aa` |
| `scratch/ontology_pipeline_candidates/projection/schema.sql` | `c6334a1184a8fd40830c9e357900cbbc4caf82ec63091639d346f9acb843b230` |
