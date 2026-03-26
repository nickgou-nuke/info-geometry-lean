# Infra Tools

This directory contains the maintained infrastructure entrypoints for graph refresh, theorem-surface analysis, and build orchestration.

## Canonical entrypoints

- `refresh_decl_graph.py`
- `refresh_blueprint_tags.py`
- `run_locked_lake_build.py`
- `generate_theorem_surface_index.py`
- `generate_source_sink_compression.py`
- `generate_causal_report.py`
- `check_bipartite_bleed.py`
- `generate_structural_dedup.py`
- `generate_structural_fibers.py`
- `generate_semantic_quotient.py`
- `generate_projection_coloring.py`
- `select_openclaw_target.py`
- `canonical_policy_lint.py`

## Authoritative inputs and outputs

Authoritative graph inputs live under [artifacts/dag](/home/goutev/LEAN4/info-geometry-lean/artifacts/dag):
- `full_graph.json`
- `index/decls.jsonl`
- `index/edges.jsonl`
- `structural-topology.json`
- `source-sink-bipartite.json`

Derived readable outputs live under `reports/dag/`.

The canonical policy debt baseline for the linter lives at
`tools/infra/canonical_policy_baseline.json`.
It records both:
- current proposition-valued surfaces
- current suspect theorem surfaces

New entries in either class are forbidden unless the baseline is intentionally updated after audit.

## Maintained refresh order

```bash
python3 tools/infra/refresh_decl_graph.py
python3 tools/infra/refresh_blueprint_tags.py
python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags
python3 tools/infra/generate_theorem_surface_index.py
python3 tools/infra/generate_source_sink_compression.py
python3 tools/infra/generate_causal_report.py --out reports/dag/true-root-order.md --json-out reports/dag/true-root-order.json
python3 tools/infra/check_bipartite_bleed.py
python3 tools/infra/generate_structural_dedup.py
python3 tools/infra/generate_structural_fibers.py
python3 tools/infra/generate_semantic_quotient.py
python3 tools/infra/generate_projection_coloring.py
python3 tools/infra/select_openclaw_target.py
python3 tools/infra/canonical_policy_lint.py
```

Run these sequentially. `semantic_quotient` and `source_sink_compression` both depend on a fresh theorem-surface index.

## Operational rules

- Do not start concurrent umbrella builds; use `run_locked_lake_build.py`.
- Do not read `reports/dag/*` as current until the whole sequence has run.
- Do not update `canonical_policy_baseline.json` casually; new proposition surfaces or new suspect theorem surfaces require an explicit policy decision.
- Do not hand-edit `artifacts/dag/*` or derived reports.
- Use direct file analysis before acting on any hotspot report.

## What `canonical_policy_lint.py` now enforces

It is not only an anti-wrapper check.
It hard-fails when refreshed artifacts show any of the following regressions:
- active carriers, structural hotspots, semantic hotspots, or monochrome shells reopening
- new proposition-valued public wrapper surfaces
- new public theorem surface in canonical files without a valid `-- theorem-class: ...` tag
- new suspect public theorem surfaces in canonical files

A theorem surface is treated as suspect when it matches one or more of these failure modes:
- theorem-surface category `surrogate_or_vacuous`, `package_reprojection`, or `hypothesis_bridge`
- definitional/trivial proof shape such as `rfl`, `Iff.rfl`, one-step `simp`/`simpa`, or direct rename after unfold
- alias-like public theorem surface with no downstream theorem dependents

This makes the policy bite: theoremification debt is explicit, baseline-tracked, and CI-visible.
