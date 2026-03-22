# Commands

## Core builds

Canonical umbrella:

```bash
lake build InfoGeometry.Canonical.All
```

Full rebuild:

```bash
lake build -R
```

DAG tooling:

```bash
lake build DAG semanticBlockExport semanticBlockServer
lake build scripts.DAG.Exploration.HarvestDiagnostics
lake build scripts.DAG.Exploration.LiftNaturalityDiagnostics
lake build scripts.DAG.Exploration.NaturalityPromoter
python3 -m py_compile tools/skynet_v2.py
```

## Trusted semantic block export

Template:

```bash
python3 tools/semantic_block_export.py \
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
python3 tools/skynet_v2.py \
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
python3 tools/skynet_v2.py \
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
python3 tools/generate_auto_docs.py
```

## End-to-end documentation refresh

Using the current trusted semantic export set:

```bash
python3 tools/update_repo_docs.py
```

Refreshing the tracked heavy-module subset first:

```bash
python3 tools/update_repo_docs.py --refresh-exports
```

Refreshing every current semantic export first:

```bash
python3 tools/update_repo_docs.py --refresh-exports all
```

Refreshing tracked Lean modules changed in `HEAD` or the current index/worktree first:

```bash
python3 tools/update_repo_docs.py --refresh-exports changed
```

Absolute causal-order report from the trusted declaration graph artifacts under `.build/`:

```bash
python3 tools/generate_causal_report.py \
  --graph .build/full_graph.json \
  --decls .build/index/decls.jsonl \
  --out reports/dag/true-root-order.md \
  --json-out reports/dag/true-root-order.json
```

OpenClaw target selector from the current causal-order JSON:

```bash
python3 tools/select_openclaw_target.py \
  --input reports/dag/true-root-order.json \
  --json-out reports/dag/openclaw-targets.json \
  --md-out reports/dag/openclaw-targets.md
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

## Declaration-level exports

Forward graph:

```bash
lake env lean --run lean/DAG/ExportForwardGraph.lean \
  InfoGeometry docs-map/module_graph.json InfoGeometry
```

Skeleton:

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
