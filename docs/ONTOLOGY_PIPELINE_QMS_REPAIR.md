# Ontology pipeline repair and acceptance contract

Status: implementation and independent review in progress. This document is a
task contract, not a successful refresh, build, or QMS certificate.

## Intended result

The unified theory graph retains typed relations and provenance. Compiler
dependencies form its DAG view; equivalences, representation maps and duplicate
candidates remain distinct relations. A fingerprint match alone never permits
merging declarations. Source owners and proved compatibility remain authoritative.

The online projection must expose one completed generation per source and scope.
Historical generations remain addressable. A narrow export cannot replace the
full `InfoGeometry.All` selection. A failed import must leave selected reads
unchanged, even if staging batches have committed.

## Independent review responsibilities

The named agents below record the initial review cycle; they are historical
assignments, not active reviewers or current acceptance evidence. Every new
candidate or revised production diff requires a fresh A-A review and a separate
QA-A run against that exact snapshot.

| Role | Agent | Responsibility |
|---|---|---|
| Coordinator / G-A | Parent session | Integration, execution scheduling, evidence and source promotion |
| Export A-A | `pipeline_export_audit` | Stream integrity, provenance, receipts and exporter lifetime |
| Projection A-A | `pipeline_projection_audit` | Source identity, membership, publication and API semantics |
| QA-A | `pipeline_qa_acceptance` | Independently execute decisive checks against reviewed file hashes |
| Candidate authors | Former auditors, explicitly reassigned after reporting | Isolated topology and projection proposals under `scratch/ontology_pipeline_candidates/`; cannot independently approve their own proposals |

Initial audits requested changes; corrective source reviews passed at their
recorded scope. Subsequent source drift and new candidates require fresh
review. Candidate files and parent edits are not accepted until reviewed and
tested. Tests/builds are serialized; an occupied
execution slot is a wait condition, not a failed test or a pass.

## Required corrections and evidence

| Requirement | Evidence required before closure |
|---|---|
| Shared generation identifiers | Producer/resolver tests for ASCII, boundaries, empty IDs, hyphens and Unicode |
| Lossless stream receipt | Reject malformed records, duplicate identities and stored/emitted count mismatch; retain forward references; reject empty declarations |
| Exact edge carrier | Both endpoints belong to the selected declaration collection; actual AQL regression using a foreign but resolvable endpoint |
| Provenance | Bind executable, exporter implementation, resolved artifact map and consumed artifacts; establish source/build correspondence separately |
| Child lifecycle | Exporter is drained/reaped inside the lock on failure; no unrelated process termination |
| Complete term mapping | Malformed names and duplicate identities fail before writes; each upsert resolves all requested identities before commit |
| Source isolation | Deployment identity plus database separates equal names from different sources |
| Generation membership | Declaration payload, module membership and dependencies are scoped to immutable generations |
| Atomic publication | Complete counts, identity sets and digests reconciled before atomically selecting a generation with expected-predecessor protection |
| Coherent reads | Resolve selection once; pin pagination to that generation; reject incomplete generations and absent selections |
| Historical preservation | Removed declarations/edges disappear from G2 while G1 remains intact; no inference of historical membership from legacy additive rows |
| Deduplication | Candidate hashes descend to source statements, hypotheses and consumers; canonical reuse changes require owner validation |

## Query boundaries

The existing upstream `/api/terms` surface is a lexical term-name search over
an additive store. Shared-table related terms and `related_counts` are not Lean
dependency edges. Imported `term__term` rows do not establish that upstream
consumes them. Dependency inspection currently requires generation-selected
Arango queries; a coherent PostgreSQL view needs an explicit generation-aware
adapter with deployment authentication preserved.

Use maintained configuration for endpoints and credentials. The observed
declaration deployment is Arango `127.0.0.1:8530`, database `infogeometry`.
Do not infer it from container names or confuse it with the Hive or model ports.
Credentials must never appear in receipts, logs, source identity or this document.

## Regression and runtime evidence still required

Run the following unit files sequentially after confirming the execution slot:

- `tests/test_decl_graph_generation.py`
- `tests/test_refresh_decl_graph_executable.py`
- `tests/test_decl_graph_receipt_integrity.py`
- `tests/test_ontology_relationship_identity.py`
- `tests/test_ontology_term_integrity.py`

Then exercise database-level publication, failure recovery, same-name source
isolation, stale-edge exclusion and concurrent selected reads. Mock tests do not
establish database transaction or AQL behavior. Final QA records the exact
reviewed hashes, commands, outputs, scope and unresolved findings.

The current canonical Drazin presence sentinel is
`InfoGeometry.Canonical.DrazinEpistemicSolveEtCoagula.drazin_epistemic_solve_et_coagula_master_synthesis`.
The removed `DrazinSpeciesUnifiedPoset` owner is not a valid absence/freshness
test. Even a current sentinel's presence alone does not prove generation freshness.

## Independent QA checkpoint (2026-11-05)

The parent reviewed and promoted the independent failure-injection candidate
to `tests/test_pipeline_publication_adversarial.py`. QA reran the promoted file:

```bash
python3 -m unittest discover -s tests -p test_pipeline_publication_adversarial.py -v
```

Result: exit 0, 15 tests, 14 passed and one opt-in AQL test skipped. The tested
file SHA-256 is
`46e61238e3c4f8d8febef3f4bcf99d0b269c059f83d1621afe69f765773d2554`.
These tests exercise malformed/duplicate records, count loss, forward
references, foreign endpoints, source/artifact drift, child cleanup, literal
credential transport, and incomplete relationship iteration. They do not
establish atomic PostgreSQL publication or freshness of a live generation.

Independent locked `dagIndexer` build and direct `lean/DAG/Indexer.lean`
elaboration both returned exit 0. Warnings were present. The strict screener
returned exit 1 with 12 T17 findings on exporter data structures; that remains
a reported failed gate requiring scope review, not a clean Gate 0 result.
An independent follow-up reproduced the current failure with
`python3 tools/infra/opengauss_screener.py --strict lean/DAG/Indexer.lean`:
exit 1 with warnings for `DeclNode`, `StreamEdge`, `DepEdge`, `Morphism`,
`EdgeKey`, `TypeNode`, `FullGraph`, `EdgeLeakageReport`, `ArtifactMeta`,
`IndexerState`, `PendingConstant`, and `EdgeFilterResult`. The historical
record did not preserve its exact command, so this is a current reproduction,
not proof of the original invocation. The owner contains concrete producers
for these serialization and state records, while T17 currently recognizes
closed witnesses rather than those producer paths. Keep this strict finding
open for an explicit schema-versus-mathematical-model policy; do not add dummy
`Inhabited` values or disable T17 globally.

The topology audit findings for key identity and SCC classification are
corrected in the current working-tree candidate. The hydrator now resolves
persisted vertex keys, preserves canonical keys through raw and membership-edge
imports, marks singleton self-loops cyclic, and separates internal SCC evidence
from inter-component quotient arcs. The importer accepts explicit source
collection mappings; the descent verifier selects the matching witness role.
Independent A-A passed the exact source diff, and separate QA-A ran:

```bash
PYTHONPATH=src:. /home/goutev/miniforge3/envs/sage/bin/python -m pytest -q tests/test_hydrate_arango_topology.py
PYTHONPATH=src:. /home/goutev/miniforge3/envs/sage/bin/python -m pytest -q tests/test_opengauss_cli.py
```

Results: 6 topology tests and 24 CLI tests passed. These are unit tests; no
live Arango import or AQL descent check was run. The causal-cone packet builder
finding remains open: explicit collection overrides are not yet bound to the
receipt that authorizes them. Generation-scoped projection, atomic publication,
and coherent selected reads also remain open under the requirements above.
No overall ontology-unification acceptance follows from these focused checks.

Review snapshot evidence: A-A read-only PASS covered `hydrate_arango_topology.py`
(`6734e08928935d2d2686a163ea9c0966aa2c6ca35a6728ddc42543b52dcae11e`),
`arango_layered_ingest.py`
(`989f659ccd367221adeccf7ae32cdf2dbce73a119cf57d0d3768065a1cb97834`), and
`verify_layered_arango_descent.py`
(`c70ff079dce979729b5098f1e2c9f97d4ba309edc342a41f93b9b4ffb3a35d03`). QA-A
confirmed test hashes `test_hydrate_arango_topology.py`
(`0d6d26ab844ba5744b2a55b38656e9b777f49c4b638f4ddc28e2f8c4d0ecc66f`) and
`test_opengauss_cli.py`
(`bea4591e41779c12b5051bf65e01188d772d87ab4cdb146697ec8cb148ebae16`).
