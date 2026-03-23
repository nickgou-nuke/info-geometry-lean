# Commands

## Core builds

Canonical umbrella:

```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.Canonical.All
```

Full rebuild:

```bash
python3 tools/infra/run_locked_lake_build.py -R
```

DAG tooling:

```bash
lake build DAG semanticBlockExport semanticBlockServer
lake build scripts.DAG.Exploration.HarvestDiagnostics
lake build scripts.DAG.Exploration.LiftNaturalityDiagnostics
lake build scripts.DAG.Exploration.NaturalityPromoter
python3 -m py_compile tools/frontier/skynet_v2.py
```

## Authoritative declaration DAG and blueprint workflow

Refresh the public declaration graph and the LeanArchitect-facing blueprint surface:

```bash
python3 tools/infra/refresh_decl_graph.py
python3 tools/infra/refresh_blueprint_tags.py
python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags
python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags:blueprint
python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags:blueprintJson
```

The declaration DAG lives in `artifacts/dag/`.
That refresh emits `full_graph.json`, `index/decls.jsonl`, and the native `structural-topology.json` artifact before the source-sink correspondence layer is regenerated.
The human-facing blueprint workflow is documented in `blueprint/README.md`.

## Trusted semantic block export

Template:

```bash
python3 tools/frontier/semantic_block_export.py \
  lean/InfoGeometry/Canonical/<Module>.lean \
  reports/dag/<Module>.semantic-block.stdlib.json \
  --server-mode stdlib \
  --inject-rpc-import \
  --skip-wait-for-diagnostics \
  --timeout 900 \
  --transcript reports/dag/<Module>.semantic-block.stdlib.transcript.jsonl \
  --stderr-log reports/dag/<Module>.semantic-block.stdlib.stderr.log
```

Known-good heavy examples:
- `GrandSynthesis`
- `AnalyticalIndex`
- `WeylTransport`
- `KasparovCycle`
- `OperatorAlgebraBridge`

## Frontier discovery

Reverse consumer search from the KK seed:

```bash
python3 tools/frontier/skynet_v2.py \
  --input reports/dag/KasparovCycle.semantic-block.stdlib.json \
  --input reports/dag/AnalyticalIndex.semantic-block.stdlib.json \
  --input reports/dag/OperatorAlgebraBridge.semantic-block.stdlib.json \
  --input reports/dag/GrandSynthesis.semantic-block.stdlib.json \
  --seed KasparovCycle.analyticalIndex \
  --walk reverse \
  --top 12 \
  --json-out reports/dag/skynet-v2-frontier-reverse.json \
  --md-out reports/dag/skynet-v2-frontier-reverse.md
```

Local bridge kernel around the seed:

```bash
python3 tools/frontier/skynet_v2.py \
  --input reports/dag/KasparovCycle.semantic-block.stdlib.json \
  --input reports/dag/AnalyticalIndex.semantic-block.stdlib.json \
  --input reports/dag/OperatorAlgebraBridge.semantic-block.stdlib.json \
  --input reports/dag/GrandSynthesis.semantic-block.stdlib.json \
  --seed KasparovCycle.analyticalIndex \
  --walk both \
  --top 12 \
  --json-out reports/dag/skynet-v2-frontier.json \
  --md-out reports/dag/skynet-v2-frontier.md
```

## Generated status page

```bash
python3 tools/docs/generate_auto_docs.py
```

## End-to-end documentation refresh

Using the current trusted semantic export set:

```bash
python3 tools/docs/update_repo_docs.py
```

Refreshing the tracked heavy-module subset first:

```bash
python3 tools/docs/update_repo_docs.py --refresh-exports
```

Refreshing every current semantic export first:

```bash
python3 tools/docs/update_repo_docs.py --refresh-exports all
```

Refreshing tracked Lean modules changed in `HEAD` or the current index/worktree first:

```bash
python3 tools/docs/update_repo_docs.py --refresh-exports changed
```

Refresh the public authoritative declaration graph, native structural topology, and regenerate the causal-order report:

```bash
python3 tools/infra/refresh_decl_graph.py

python3 tools/infra/generate_causal_report.py \
  --out reports/dag/true-root-order.md \
  --json-out reports/dag/true-root-order.json
```

Native structural hotspot refresh plus OpenClaw target selection:

```bash
python3 tools/infra/generate_source_sink_compression.py

python3 tools/infra/check_bipartite_bleed.py

python3 tools/infra/select_openclaw_target.py \
  --input reports/dag/true-root-order.json \
  --structural-hotspots reports/dag/structural-hotspots.json \
  --json-out reports/dag/openclaw-targets.json \
  --md-out reports/dag/openclaw-targets.md
```

Theorem-surface classifier from the current declaration export and live debt indices:

```bash
python3 tools/infra/generate_theorem_surface_index.py \
  --md-out reports/dag/theorem-surface-index.md \
  --json-out reports/dag/theorem-surface-index.json
```

Declaration DAG NetworkX export, readable module plot, and filtered theorem-surface frontier view:

```bash
python3 tools/infra/plot_decl_graph.py \
  --decl-graphml-out reports/dag/declaration-networkx.graphml \
  --module-graphml-out reports/dag/module-networkx.graphml \
  --module-svg-out reports/dag/module-networkx.svg \
  --frontier-decl-graphml-out reports/dag/declaration-networkx-frontier.graphml \
  --frontier-module-graphml-out reports/dag/module-networkx-frontier.graphml \
  --frontier-module-svg-out reports/dag/module-networkx-frontier.svg \
  --frontier-hotspot-graphml-out reports/dag/module-networkx-frontier-hotspots.graphml \
  --frontier-hotspot-svg-out reports/dag/module-networkx-frontier-hotspots.svg \
  --frontier-hotspot-json-out reports/dag/module-networkx-frontier-hotspots.json \
  --frontier-burndown-md-out reports/dag/frontier-burndown.md \
  --frontier-burndown-json-out reports/dag/frontier-burndown.json
```

Source-bundle / sink-bundle compression layer and incidence graph:

```bash
python3 tools/infra/generate_source_sink_compression.py \
  --structure artifacts/dag/structural-topology.json \
  --artifact-out artifacts/dag/source-sink-bipartite.json \
  --md-out reports/dag/source-sink-compression.md \
  --json-out reports/dag/source-sink-compression.json \
  --graphml-out reports/dag/source-sink-incidence.graphml \
  --svg-out reports/dag/source-sink-incidence.svg
```

Native structural anti-bleed diagnostic:

```bash
python3 tools/infra/check_bipartite_bleed.py \
  --structure artifacts/dag/structural-topology.json \
  --bipartite artifacts/dag/source-sink-bipartite.json \
  --json-out reports/dag/structural-anti-bleed.json \
  --md-out reports/dag/structural-anti-bleed.md
```

ConformalUnification topological patch and prompt packet:

```bash
python3 tools/frontier/extract_module_patch.py \
  --seed-module InfoGeometry.Canonical.ConformalUnification \
  --json-out reports/dag/ConformalUnification-topological-patch.json \
  --md-out reports/dag/ConformalUnification-topological-patch.md \
  --graphml-out reports/dag/ConformalUnification-topological-patch.graphml \
  --svg-out reports/dag/ConformalUnification-topological-patch.svg
```

Self-optimization cycle sheet:

```bash
python3 tools/generate_self_optimization_report.py
```

Surrogate debt index:

```bash
python3 tools/generate_surrogate_index.py
```

Vacuity / alias-debt index:

```bash
python3 tools/generate_vacuity_index.py
```

Bridge thinness index:

```bash
python3 tools/generate_bridge_thinness_index.py
```

Unification index:

```bash
python3 tools/generate_unification_index.py
```

Debt-targeted replacement packet:

```bash
python3 tools/generate_debt_candidates.py
```

Dual LLM frontier prompts:

```bash
python3 tools/generate_llm_frontier_prompts.py
```

Dual LLM debt-replacement prompts:

```bash
python3 tools/generate_llm_debt_prompts.py
```

Generate the bridge-candidate packet directly from the current trusted frontier:

```bash
python3 tools/generate_bridge_candidates.py
```

Dry isolated optimization cycle:

```bash
python3 tools/run_optimization_cycle.py
```

This reuses the persistent optimization lab by default.
It also hydrates that lab from the main repo's local `.lake` cache before the
targeted build.

Dry isolated optimization cycle with an explicit frontier row and tracked
candidate packet selection:

```bash
python3 tools/run_optimization_cycle.py \
  --frontier-index 0 \
  --candidate-index 0
```

Dry isolated optimization cycle with an external proof-attempt hook and one
compiler-feedback retry:

```bash
python3 tools/run_optimization_cycle.py \
  --frontier-index 0 \
  --candidate-index 0 \
  --proof-attempt-command 'python3 tools/proof_driver.py --context {context_json}' \
  --proof-attempt-retries 1
```

Do not run the raw tracked debt packet directly (it is report-only):

```bash
python3 tools/run_optimization_cycle.py \
  --candidate-packet skills/info-geometry-repo/references/debt-candidates.md \
  --candidate-index 0
```

Instead, run against a reviewed debt packet carrying a concrete quarantine-ready sketch:

```bash
python3 tools/run_optimization_cycle.py \
  --candidate-packet <reviewed-debt-candidates.md> \
  --candidate-index 0
```

Dry isolated optimization cycle against a reviewed bridge packet carrying a
concrete quarantine-ready sketch:

```bash
python3 tools/run_optimization_cycle.py \
  --candidate-packet skills/info-geometry-repo/references/bridge-reviewed-candidates.md \
  --candidate-index 0 \
  --proof-attempt-command 'python3 tools/proof_driver.py --context {context_json}' \
  --proof-attempt-retries 1
```

Force a fresh sterile worktree only when you explicitly want a cold baseline:

```bash
python3 tools/run_optimization_cycle.py \
  --fresh-worktree \
  --frontier-index 0 \
  --candidate-index 0
```

Reuse a specific existing lab directly:

```bash
python3 tools/run_optimization_cycle.py \
  --reuse-worktree /tmp/info-geometry-autoopt/current \
  --frontier-index 0 \
  --candidate-index 0
```

Remove a worktree only when you explicitly want to discard it:

```bash
python3 tools/run_optimization_cycle.py \
  --fresh-worktree \
  --cleanup-worktree \
  --frontier-index 0 \
  --candidate-index 0
```

## Compatibility / auxiliary declaration exports

The authoritative declaration-DAG workflow is the `artifacts/dag/` lane above.
Use the commands below only for compatibility checks or one-off auxiliary diagnostics.

Legacy forward/module-graph export: archived.

If you need the old docs-map/module_graph lane for historical comparison, use the archived helper under `archive/legacy/scripts/make_graph.py`.

Auxiliary skeleton export:

```bash
lake env lean --run lean/DAG/SkeletonExport.lean \
  InfoGeometry InfoGeometry docs-map/skeleton.json
```

## Categorical diagnostics

```bash
lake env lean --run lean/scripts/DAG/Exploration/HarvestDiagnostics.lean
lake env lean --run lean/scripts/DAG/Exploration/LiftNaturalityDiagnostics.lean
lake env lean --run lean/scripts/DAG/Exploration/NaturalityPromoter.lean
lake env lean --run lean/scripts/DAG/Exploration/SquarePromoter.lean
```
