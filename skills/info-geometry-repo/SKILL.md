---
name: info-geometry-repo
description: Use when working inside the InfoGeometry Lean 4 repository and you need the repo-specific bootstrap sequence, DAG/semantic-export workflows, trusted graph paths, or the current bridge/frontier map across KK, AnalyticalIndex, Rosetta, ModularAnomaly, Weyl transport, HurwitzRGFlow, and GrandSynthesis.
---

# InfoGeometry Repo

Use this skill when the task is about this repository's structure, theorem topology, DAG tooling, semantic block export, bridge closing, or safe workflow choices for heavy Lean modules.

## First Read

Read these first:

1. `/home/goutev/LEAN4/info-geometry-lean/README.md`
2. `/home/goutev/LEAN4/info-geometry-lean/lean/DAG/README.md`
3. `/home/goutev/LEAN4/info-geometry-lean/tools/README.md`

Then read only the specific reference file(s) you need from `references/`.

## Core Mental Model

The repo has two layers:

1. domain layer
- `lean/InfoGeometry/...`
- theorem library, canonical synthesis modules, KK layer, gauge/transport/index modules

2. tooling layer
- `lean/DAG/`
- `lean/scripts/DAG/Exploration/`
- `tools/frontier/semantic_block_export.py`

Do not mix these graph views:

1. declaration DAG
- global topology, SCCs, dominators, bottlenecks, and atomic theorem truth

2. source-sink bipartite correspondence artifact
- source bundles, hydrated carriers, repeated path motifs, witness counts, and compression potential

3. block export
- source attribution, slices, quiver emission

4. semantic block graph
- purified human-facing theory structure using `primaryProduces`

For large files, semantic block export through the external stdlib server path is the trusted route.

Artifact placement matters:
- `artifacts/dag/full_graph.json` and `artifacts/dag/index/decls.jsonl` are the public authoritative atomic declaration-DAG inputs for causal-order analysis.
- `artifacts/dag/structural-topology.json` is the public authoritative native structural-analysis layer with stable condensation ids, membership, dominators, and canonical root-witness paths.
- `artifacts/dag/source-sink-bipartite.json` is the public authoritative correspondence object between atomic declaration truth and hydrated readable carriers.
- `.build/` remains a transient build cache and explicit compatibility fallback, not the documented public DAG surface.
- `reports/dag/*.semantic-block.stdlib.json` are trusted semantic block exports.
- `reports/dag/true-root-order.{md,json}`, `reports/dag/openclaw-targets.{md,json}`, and the GraphML / SVG source-sink views are derived reports and should be regenerated, not hand-maintained.
- If those layers disagree, trust the atomic DAG first, then the native structural topology, then the bipartite correspondence artifact, and regenerate the `reports/dag/` views.

## Hard Proof Policy

Treat vacuous success as failure for frontier accounting.

- Do not accept `sorry`, `admit`, `axiom`, placeholder contracts, or equivalent proof gaps on the stable theory path.
- Treat `trivial`, direct assumption unpacking, alias transport, and definitional repackaging as packaging, not proof progress.
- Only count a result as real closure when it starts from existing concrete repo data, constructs the needed witness or bridge in Lean, and proves a nonvacuous relation or invariant.
- If a theorem is assumption-driven, façade-level, or merely transport bookkeeping, label it explicitly as such.
- Never present a conditional wrapper or restated hypothesis as completed unification.

## Current DAG Pipeline Order

For the maintained DAG pipeline, use this exact order:

1. `python3 tools/infra/refresh_decl_graph.py`
2. `python3 tools/infra/refresh_blueprint_tags.py`
3. `python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags`
4. `python3 tools/infra/generate_source_sink_compression.py`
5. `python3 tools/infra/generate_causal_report.py --out reports/dag/true-root-order.md --json-out reports/dag/true-root-order.json`
6. `python3 tools/infra/check_bipartite_bleed.py`
7. `python3 tools/infra/generate_structural_dedup.py`
8. `python3 tools/infra/generate_structural_fibers.py`
9. `python3 tools/infra/select_openclaw_target.py`

Important:
- do not run `generate_source_sink_compression.py` before `refresh_decl_graph.py` has completed
- do not trust `reports/dag/*` until the whole sequence above has finished
- blueprint refresh belongs in the maintained path because stale `auto_blueprints.lean` breaks the auxiliary theorem surface

## Default Workflow

1. Identify the task type:
- whole-repo topology
- single heavy-file semantic export
- categorical diagnostics
- bridge/frontier analysis

2. Build only what you need first.

3. For full or umbrella builds, use `python3 tools/infra/run_locked_lake_build.py ...` and never start two of them concurrently.

4. Prefer semantic block export for heavy capstone modules.

5. Treat generated `reports/dag/` artifacts as disposable outputs, not tracked source.

## Trusted Heavy-File Export Path

Use:

```bash
python3 tools/frontier/semantic_block_export.py \
  <input.lean> \
  <output.json> \
  --server-mode stdlib \
  --inject-rpc-import \
  --skip-wait-for-diagnostics \
  --timeout 900
```

Why:
- separate `lean --server` process
- avoids in-process `[init]` collisions
- gives the trusted semantic block JSON for Mathlib-heavy files

## Current Frontier Map

The current visible bridge picture is multi-spined:

- KK / index trunk: `InfoGeometry.KK.KasparovCycle` -> `InfoGeometry.Canonical.AnalyticalIndex` -> `InfoGeometry.Canonical.GrandSynthesis`
- Rosetta / modular trunk: `BogoliubovFockSuper`, `TomitaTakesaki`, `InfoGeometry.Quantum.ModularAnomaly`, `InfoGeometry.Canonical.Rosetta`
- Weyl transport branch: `WeylGaugeField`, `WeylTransport`, `WeylInformationGauge`, then into Rosetta's KK and Jordan/KKT bridge theorems
- discrete / RG branch: `InfoGeometry.Quantum.Hurwitz`, `InfoGeometry.Quantum.HurwitzRGFlow`, `InfoGeometry.Canonical.RGFlow`
- finite phase branch: `InfoGeometry.Quantum.KitaevChain`

Thin adjunct modules such as `CompactOperatorBridge`, `Product`, and `KasparovCompactOperator` are not the main articulation hubs.

## Use References

- For commands and standard runs: read `references/commands.md`
- For module/frontier orientation: read `references/module-map.md`
- For prompt-ready bridge exploration over the current KK -> AnalyticalIndex -> GrandSynthesis frontier:
  read `references/frontier-prompt.md`
- For the split creative/critical LLM evaluation workflow over the current trusted frontier:
  read `references/frontier-prompt-creative.md` and `references/frontier-prompt-critical.md`
- For the current first-strike candidate bridge lemmas on that frontier:
  read `references/bridge-candidates.md`

## Agent Discipline

- Build before assuming a path is stable.
- Prefer local graph evidence over intuition.
- Use LLM reasoning as frontier proposal, not as proof authority.
- The right output is: candidate bridge statements, closure gaps, and attack plans.
- The Lean kernel decides what is true.
