# Codebase Functionality and Structure Audit (2026-03-19)

## Scope
This audit captures verified findings about repository functionality and architecture, with emphasis on:

- Lean theorem-library structure and publication surfaces.
- DAG and semantic-export tooling used to analyze theory topology.
- Python orchestration and report/document generation pipeline.
- Quality gates enforcing stable-surface and constructivity policies.

## Phase 1 Findings (Verified)

### 1. Repository identity
The repository is intentionally dual-purpose:

- A large Lean 4 formalization library under `lean/InfoGeometry`.
- A meta-analysis stack that extracts and analyzes declaration/block/semantic graphs.

Primary confirmation points:

- `README.md`
- `lean/DAG/README.md`
- `docs/auto/index.md`

### 2. Lean entrypoint and layering
The stable publication surface is layered as:

1. `lean/InfoGeometry.lean`
2. `lean/InfoGeometry/Library.lean`
3. `lean/InfoGeometry/Canonical/All.lean`

`InfoGeometry.Generated` is imported through the public root, enabling generated additions while keeping a canonical umbrella.

### 3. Build/package structure
`lakefile.lean` defines:

- Lean libraries (`InfoGeometry`, `DAG`, `Docs`, `Socratic`, etc.).
- Lean executables for semantic export server/client wrappers.
- Project scripts (`strictCheck`, `semanticAudit`, `graphToBlueprint`).

Python packaging (`pyproject.toml`) exposes a console entrypoint backed by `scripts/cli.py`, with subcommands mapped to analysis/docs modules.

### 4. Theory content organization
The canonical umbrella imports many domain modules (geometry, convex/KL, KK/index, gauge/thermo/operator-algebra bridges, capstones).

Representative files inspected:

- `lean/InfoGeometry/Basic.lean`
- `lean/InfoGeometry/Core/UnifiedGeometry.lean`
- `lean/InfoGeometry/Canonical/Foundations.lean`
- `lean/InfoGeometry/KK/KasparovCycle.lean`
- `lean/InfoGeometry/Canonical/AnalyticalIndex.lean`
- `lean/InfoGeometry/Canonical/OperatorAlgebraBridge.lean`
- `lean/InfoGeometry/Canonical/GrandSynthesis.lean`

### 5. DAG subsystem capabilities
The `lean/DAG` subsystem provides:

- Dependency graph extraction from Lean environments.
- SCC/topological/dominator analysis.
- Block provenance export and semantic block graph construction.
- RPC/server export hooks for robust external semantic export.
- Diagnostics for morphism/naturality/square promotion workflows.

### 6. Trusted semantic export workflow
The trusted path for heavy modules is externalized:

Python orchestrator -> Lean server RPC -> semantic block JSON artifacts.

Key components:

- `tools/semantic_block_export.py`
- `lean/scripts/DAG/Exploration/SemanticBlockServer.lean`
- `lean/scripts/DAG/Exploration/SemanticBlockExport.lean`

### 7. Frontier/diffusion analysis
`tools/skynet_v2.py` performs report-only frontier exploration over trusted semantic block JSONs. Repository docs currently track verified KK -> AnalyticalIndex -> GrandSynthesis bridge fronts.

### 8. Documentation generation pipeline
Generated documentation artifacts are produced through:

- Graph export (`lean/InfoGeometry/GraphExport.lean`, `scripts/analysis/make_graph.py`)
- Doc map/build steps (`scripts/docs/build_doc_map.py`)
- Blueprint conversion (`scripts/docs/graph_to_blueprint.py`)
- Auto status synthesis (`tools/generate_auto_docs.py`, `tools/update_repo_docs.py`)

### 9. Stability and quality controls
`scripts/quality/strict-check.sh` composes repository safety checks including:

- canonical surface elaboration/build checks,
- quarantine boundary enforcement,
- constructivity and surrogate audits,
- naming/docstring/style audits.

### 10. Stable vs quarantined policy
There is an explicit quarantine policy with reasons per module in:

- `scripts/quality/quarantine_manifest.txt`
- `lean/InfoGeometry/Unstable/Quarantine.lean`

This separates canonical publication pathways from modules flagged for vacuity/surrogate concerns.

## Phase 2 Findings (Functionality + Structure)

### 11. Functional map by module cluster
Directory-level file counts under `lean/InfoGeometry` show where most active formalization effort is concentrated:

- `Canonical`: 164 files (main publication/synthesis surface)
- `Krein`: 24 files
- `Projective`: 17 files
- `Clifford`: 16 files
- `ExponentialFamily`: 11 files
- `Core`: 11 files
- `MaxEnt`: 10 files

Total counts from local scan:

- `lean/InfoGeometry` Lean files: 372
- `lean/InfoGeometry/Canonical` Lean files: 164
- `lean/DAG` Lean files: 31

Role summary by cluster:

- `Core`, `Basic`: foundational geometric/probability definitions used across canonical modules.
- `KL`, `MaxEnt`, `Convex`, `Geometry`: information-theoretic and convex-geometric base layer.
- `KK`, `Krein`, `Clifford`: index/operator-algebraic and graded-structure substrate.
- `Canonical`: bridge, synthesis, and publication-facing theorem surface.
- `Unstable`: quarantine surface for modules with documented vacuity/surrogate concerns.

### 12. End-to-end workflow map

#### 12.1 Build and quality gate pipeline
Primary controls:

- CI workflow: `.github/workflows/ci.yml`
- strict local gate: `scripts/quality/strict-check.sh`
- quarantine enforcement: `scripts/enforce_quarantine_imports.sh`

Core outputs:

- successful canonical/build verification
- rejection of forbidden canonical imports (archive/experimental)
- constructivity/surrogate/style/naming/docstring audit outcomes

#### 12.2 Declaration graph export pipeline
Pipeline:

1. `lean/InfoGeometry/GraphExport.lean`
2. `scripts/analysis/make_graph.py`
3. generated `docs-map/graph.json` and `docs-map/module_graph.json`

Current `docs-map/module_graph.json` stats in this snapshot:

- discovered modules: 227
- graph nodes: 227
- import edges: 520
- buildable modules: 197
- non-buildable modules: 30
- connected components: 5
- largest component: 223

#### 12.3 Trusted semantic block export pipeline
Pipeline:

1. `tools/semantic_block_export.py` (external orchestrator)
2. Lean RPC server path via `lean/scripts/DAG/Exploration/SemanticBlockServer.lean`
3. semantic export methods in DAG server/export modules
4. generated semantic-block JSONs under `reports/dag/`

This is the documented trusted route for heavy files.

#### 12.4 Frontier analysis pipeline
Pipeline:

1. semantic block JSON inputs
2. `tools/skynet_v2.py` diffusion over semantic graph
3. frontier packets (`reports/dag/skynet-v2-frontier*.json|md`)
4. consolidated auto status via `tools/generate_auto_docs.py` / `tools/update_repo_docs.py`

#### 12.5 Docs/onboarding pipeline
Current onboarding and orientation surface now includes:

- `README.md`
- `NEWCOMER_PATH.md`
- `archive/README.md`
- `archive/legacy/README.md`

This gives a cleaner "current vs legacy" route before diving into DAG internals.

### 13. Stable vs quarantine boundaries (verified)

#### 13.1 Explicit quarantine registry
Quarantine registry contains 35 non-comment entries:

- `scripts/quality/quarantine_manifest.txt`
- import umbrella: `lean/InfoGeometry/Unstable/Quarantine.lean`

#### 13.2 Enforcement controls
Boundary controls are present in both CI and local scripts:

- `.github/workflows/ci.yml` checks canonical imports for forbidden archive/experimental edges.
- `scripts/enforce_quarantine_imports.sh` enforces manifest-defined quarantine boundaries.
- `scripts/audit_surrogates.sh` guards against stable-surface imports of unstable modules.

Observed import scan for `InfoGeometry.Unstable.*` from `lean/InfoGeometry` shows occurrences only in `lean/InfoGeometry/Unstable/Quarantine.lean` in this snapshot.

### 14. Coupling and hotspot indicators

#### 14.1 Canonical import frequency hotspots
Most frequent canonical imports (top sample from local scan):

- `InfoGeometry.Canonical.SpectralInference` (17)
- `InfoGeometry.Convex.HessianGeometry` (11)
- `InfoGeometry.Canonical.Drazin` (11)
- `InfoGeometry.Canonical.TomitaTakesaki` (10)
- `InfoGeometry.Canonical.MoorePenrose` (10)
- `InfoGeometry.Canonical.ConformalUnification` (10)
- `InfoGeometry.Canonical.RicciMongeAmpere` (9)

This indicates high cross-coupling around spectral/inference, algebraic inverses, modular/Tomita, and Ricci-Monge-Ampere bridges.

#### 14.2 Umbrella-level coupling anchors
Additional direct-import probes in canonical modules:

- imports of `InfoGeometry.Core*`: 10
- imports of `InfoGeometry.Canonical.Foundations`: 1 (the umbrella itself is a large importer)
- imports of `DAG.Basic`: 1 (at canonical umbrella layer)

Interpretation:

- `Canonical/All.lean` acts as a high fan-in publication aggregator.
- frequently reused bridge modules become practical coupling anchors.
- DAG tooling remains intentionally reachable from publication-level assembly.

### 15. Structural risk and technical-debt signals (evidence-based)

- High breadth at `Canonical/` (164 files) increases impact radius of cross-cutting edits.
- Quarantine set size (35 modules) is material and should remain visible in release-quality planning.
- Module graph reports 30 non-buildable modules in current generated topology snapshot; these should be interpreted alongside archive-draft policy checks.
- Repository carries multiple generated/report artifacts that are intentionally untracked (`reports/dag/`), requiring disciplined regeneration rather than manual edits.
- `NEWCOMER_PATH.md` and archive readmes reduce onboarding ambiguity and help keep contributors on the supported surface before historical archaeology.

## Remaining Research Gaps
Phase 2 addressed functionality/structure mapping at repository level. Remaining deep-dive items (optional next pass):

- declaration-level call/dependency pressure ranking beyond import-level counts;
- per-cluster test/proof maturity metrics;
- longitudinal trend analysis across prior theory audits.

## Status
Phase 1 completed.
Phase 2 completed.
Audit now contains both baseline and deeper functionality/structure findings.
