---
name: info-geometry-repo
description: Use when working inside the InfoGeometry Lean 4 repository and you need the repo-specific theorem spine, DAG workflow, trusted artifact order, or the current representation-depth model.
---

# InfoGeometry Repo

Use this skill for repo topology, DAG refresh, canonical bridge ownership, theorem-surface debt, representation-depth audits, and safe workflow choices on heavy files.

If the task is about canonical theorem ownership or wrapper elimination, also read `skills/lean-canonicalization-policy/SKILL.md`.
For the repo's creative self-description of the agent role, also read `docs/black_books/08_the_agentic_caretaker.md`.

## Read First

Read these in order:
1. `README.md`
2. `lean/InfoGeometry/Audit.lean`
3. `docs/OperationalIntent.md`
4. `docs/Theory.md`
5. `lean/DAG/README.md`
6. `tools/infra/README.md`

Then read only the specific reference or source files you need.

## Core Mental Model

The repo has three maintained surfaces:
1. domain layer under `lean/InfoGeometry/`
2. Lean-native architecture enforcement under `lean/InfoGeometry/Meta/` and `lean/InfoGeometry/Audit.lean`
3. tooling layer under `lean/DAG/`, `tools/infra/`, and `tools/frontier/`

The repo is one theory with several presentations.
The main formal burden is not to collapse those presentations into one surface, but to enforce the morphisms between them honestly.
Read stable files as owner, translator, coherence, or capstone surfaces over the same underlying theory.

The stable theory spine uses a native **semantic taxonomy** (`RepDepth` in `Architecture.lean`),
not the old numeric L0–L5 system. Tags are `@[rep_depth <level>]`:

| `@[rep_depth ...]` | Presentation |
|---------------------|-------------|
| `count` | Raw relative counts and measure theory |
| `projective` | Positive rays, normalization, gauge |
| `operator` | Diagonal operator lift, partition calculus |
| `krein` | Split quadratic geometry, Clifford atoms |
| `transport` | Bogoliubov flows, spectral transport |
| `thermo` | Gibbs states, Sinkhorn, attention surfaces |

Adjacency: a non-`@[capstone]` declaration at depth `d` may only depend on depth `d` or `d − 1`.
This is enforced by `#audit_architecture` in `Audit.lean` at build time.

Stable files should be read as exactly one of:
- owner
- translator
- coherence file
- capstone consumer

The DAG and Python layers are maintained memory.
Use them to restore context, surface transport pressure, and choose what to read next.
Do not use them to replace Lean source or invent ontology absent from code.

## Multilingual Bridge Comment Policy

This repository is a Lean 4 formalization of the physics of information. It
uses established language from information geometry, statistical mechanics,
operator algebra, quantum mechanics, and thermodynamics because that is the
least obscure vocabulary for the structures being formalized.

Treat bridge-bearing comments and docstrings as part of the representation
layer, not as disposable prose. They may encode the transport between SymPy,
Python, Lean 4, LaTeX, and natural mathematical language.

Do not judge modules by comment-to-code ratio, prose length, or the mere
presence of physically loaded terms. Judge semantic faithfulness, theorem
ownership, dependency connectivity, and bridge correctness.

When editing comments:
- preserve or expand cross-representation explanations
- correct false or stale interpretation
- distinguish analogy, definition, and theorem
- delete only prose that is false, duplicative, stale, or not bridge-bearing

LeanTrail memory carriers are now also maintained retrieval surfaces:
- canonical snapshot: `artifacts/leantrail/graph_snapshot.json`
- external adapters: GraphML / Neo4j CSV / Arango JSON
- conformance gate must pass before treating any external carrier as valid memory

## Trust Order

If surfaces disagree, trust in this order:
1. Lean source
2. the native audit entrypoint
3. atomic DAG artifacts under `artifacts/dag/` (verified via `index/meta.json` schema version and timestamp)
4. structural and source-sink artifacts
5. derived reports under `reports/dag/`
6. conceptual docs

## Artifact Verification

Before trusting any DAG artifact, check `artifacts/dag/index/meta.json`:
- `schemaVersion`: must be ≥ 2 (current version)
- `timestamp`: ISO UTC of last refresh
- `nodeCount` / `edgeCount`: should match expected cardinality
- `oleanHash`: if present, confirms which build produced the artifacts

The full artifact set under `artifacts/dag/` is:
- `full_graph.json` — declaration DAG
- `structural-topology.json` — SCC-level metadata
- `source-sink-bipartite.json` — packet and carrier incidence
- `representation-depth-tags.json` — depth grammar tags
- `index/meta.json` — schema version, counts, timestamp, olean hash
- `index/decls.jsonl` — declaration metadata
- `index/edges.jsonl` — dependency edges
- `index/morphisms.jsonl` — recognized morphisms
- `index/types.jsonl` — type-node records
- `process-flow/` — transport evidence (flow-edges, process-events, flow-cocycles, comparison-candidates, lawful-path-candidates, defects)

LeanTrail memory-carrier artifacts under `artifacts/leantrail/`:
- `graph_snapshot.json` — canonical LeanTrail snapshot
- `graph_snapshot.graphml` — GraphML adapter
- `neo4j/{nodes.csv,edges.csv,metadata.json}` — Neo4j CSV adapter
- `arango/{ig_nodes.jsonl,ig_edges.jsonl,metadata.json}` — Arango JSON adapter
- `conformance_*.{json,md}` — adapter parity reports

## Hard Proof Policy

Treat vacuous success as failure.
- no `sorry`, `admit`, `axiom`, or equivalent gaps on the stable path
- trivial transport and aliasing do not count as proof progress
- capstone claims are only real when composed from lower repo owners already present
- existential witnesses must be genuine dependencies
- do not use `∃ h : P, (let _ := h; Q)` as a linter workaround when `Q` is non-dependent
- for non-dependent existence claims, prefer idiomatic `∃ _ : P, Q`

## Pauli Seal (Mandatory)

For stabilization/closure work by agents and coding agents, enforce:
1. `I.no_mask_mandate`
2. `II.functorial_connectivity`
3. `III.axiom_surface_seal`
4. `IV.multilingual_bridge_fidelity`
5. `V.identity_via_reflexivity`
6. `VI.anti_existential_hypothesis`
7. `VII.interface_witness_fidelity`
8. `VIII.metric_fidelity`
9. `IX.anti_residual_redirect`
10. `X.parameter_admission`
11. `XI.public_uniqueness_mandate`

Run:

```bash
python3 tools/quality/functorial_invariance_audit.py --json-out reports/dag/functorial-invariance-audit.json --md-out reports/dag/functorial-invariance-audit.md
python3 tools/quality/check_translation_registry.py \
  --registry docs/OperatorTheoremTranslationRegistry.md \
  --required-anchor InfoGeometry.Canonical.ModularSuperchargeClosure.superHamiltonian_eq_modularTransportGenerator_lorentzBivectorSeed \
  --required-anchor InfoGeometry.Canonical.ModularSuperchargeClosure.operatorialKMSCondition_lorentzBivectorSeed_of_structural \
  --required-anchor InfoGeometry.Canonical.ModularSuperchargeClosure.exists_lorentzBivectorGenerator_split_with_drazin_lane_centrality \
  --required-anchor InfoGeometry.Canonical.ModularSuperchargeClosure.projectedEvenGenerator_fixed_under_lorentzChiralConeOrbit \
  --required-anchor InfoGeometry.Canonical.ModularSuperchargeClosure.projectedEvenGenerator_fixed_under_lorentzWedgeOrbit \
  --required-anchor InfoGeometry.Canonical.KKTCore.uPlus_eq_gOnePart \
  --required-anchor InfoGeometry.Canonical.KKTCore.uPlus_mul_uPlus_eq_zero \
  --required-anchor InfoGeometry.Canonical.KKTCore.commutator_uPlus_uMinus_isGZero
python3 tools/quality/pauli_seal_audit.py --root lean/InfoGeometry/Canonical --json-out reports/pauli-seal-audit.json
```

Any findings block closure promotion.

## Vacuity Enforcement

A three-layer vacuity linter is available:
- **Layer A** (Lean): `lean/InfoGeometry/Lint/Vacuity.lean` — proof-shape and statement-shape checks with `@[infrastructure]`, `@[terminal]`, `@[expository]` role tags; `#vacuity_lint` and `#vacuity_lint_file` commands
- **Layer B** (Python): `tools/theorem_significance.py` — graph-level significance scoring using DAG edges; classifies V0 (syntactic vacuity), V1 (wrapper inflation), V2 (dead public theorem), V4 (bridge infrastructure promoted)
- **Layer C** (CI gate): `tools/check_vacuity_policy.py` — reads Layer B output, fails on error-level violations in bridge/canonical files

## Maintained DAG Pipeline

The DAG refresh now supports incremental skip via olean content hashing.
Use `--force` to bypass the skip when needed.

Use this exact main sequence:
1. `python3 tools/infra/run_locked_lake_build.py InfoGeometry.Audit`
2. `python3 tools/infra/refresh_decl_graph.py` (skips if oleans unchanged; use `--force` to override)
3. `python3 tools/infra/refresh_blueprint_tags.py`
4. `python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags`
5. `python3 tools/infra/generate_theorem_surface_index.py`
6. `python3 tools/infra/generate_equivalence_dictionary.py --curated-json docs/NameEquivalenceRegistry.json --json-out reports/dag/equivalence-dictionary.json --md-out reports/dag/equivalence-dictionary.md`
7. `python3 tools/infra/generate_source_sink_compression.py`
8. `python3 tools/infra/generate_causal_report.py --out reports/dag/true-root-order.md --json-out reports/dag/true-root-order.json`
9. `python3 tools/infra/check_bipartite_bleed.py`
10. `python3 tools/infra/generate_structural_dedup.py`
11. `python3 tools/infra/generate_structural_fibers.py`
12. `python3 tools/infra/generate_semantic_quotient.py`
13. `python3 tools/infra/generate_projection_coloring.py`
14. `python3 tools/infra/select_openclaw_target.py`
15. `python3 tools/infra/canonical_policy_lint.py`
16. `python3 tools/infra/generate_replacement_frontier.py`

Stable spine supplements:
- `python3 tools/infra/check_representation_depth.py`
- `python3 tools/infra/generate_representation_depth_graph.py`

Process-flow supplements:
- `lake env lean --run lean/DAG/ProcessFlowExport.lean InfoGeometry.Audit artifacts/dag/process-flow`
- `python3 tools/infra/generate_process_flow_report.py`

LeanTrail memory-carrier supplements:
- `lake script run leantrailExport --snapshot artifacts/leantrail/graph_snapshot.json --to all`
- `lake script run leantrailConformance --baseline ... --candidate ... --fail-on-violation`
- `python3 tools/leantrail/conformance.py --baseline ... --candidate ... --required-locked-paths leantrail/config/required_locks.json --fail-on-violation`
- `lake script run leantrailArangoIngest --input-dir artifacts/leantrail/arango`
- `lake script run leantrailArangoPhysicsEval --mode local --input artifacts/leantrail/arango --center <decl>`
- `lake script run leantrailFailureHarvest --defects artifacts/dag/process-flow/defects.jsonl --out artifacts/leantrail/failed_transitions.jsonl`
- `python3 tools/leantrail/failure_harvester.py --defects ... --build-stdout ... --build-stderr ... --out artifacts/leantrail/failed_transitions.jsonl --merge-existing`
- `lake script run leantrailPathLock --snapshot artifacts/leantrail/graph_snapshot.json --src <decl> --dst <decl> --state locked`
- `lake script run leantrailHolePackets --failed-transitions artifacts/leantrail/failed_transitions.jsonl`
- `bash scripts/quality/strict-check.sh` (on failure auto-harvests logs into `artifacts/leantrail/failed_transitions.jsonl`)

## Default Workflow

0. Refresh the maintained name-equivalence dictionary:
   `python3 tools/infra/generate_equivalence_dictionary.py --curated-json docs/NameEquivalenceRegistry.json --json-out reports/dag/equivalence-dictionary.json --md-out reports/dag/equivalence-dictionary.md`
1. Identify whether the task is source ownership, proof stabilization, graph refresh, or heavy-file frontier work.
2. Read the target file and direct consumers before trusting any report.
3. Check `artifacts/dag/index/meta.json` timestamp to confirm artifacts are current.
4. Use locked builds for umbrella targets.
5. Run the Lean-native audit before trusting Python layer reports.
6. Use DAG reports to choose the next file, not to replace code reading.
7. Prefer representation-depth reports for rendered layer grammar and hotspot reports for residual debt only.
8. Use process-flow artifacts when the question is about transport, boundary, defect, or coherence pressure.
9. For external graph/database use, run LeanTrail conformance against the canonical snapshot first.

## Heavy Files

For heavy files, prefer semantic block export over guessing from the raw declaration graph:

```bash
python3 tools/frontier/semantic_block_export.py           <input.lean>           <output.json>           --server-mode stdlib           --inject-rpc-import           --skip-wait-for-diagnostics           --timeout 900
```

## Agent Discipline

- build before assuming a path is stable
- prefer direct file evidence over graph rhetoric
- keep ownership low and theorem surfaces load-bearing
- preserve real morphisms across representation levels; do not flatten them away
- the Lean kernel decides what is true
- Python reports summarize; they do not legislate architecture

## Agent Role

When acting well inside this repository, the coding agent should behave as:
- architect of lawful module shape
- creator of new, constructive structure
- caretaker who removes misleading, toy, or corrupting artefacts

This is a methodological orientation, not a permission slip to override proof,
architecture, or ontology. The kernel still decides truth.
