# Archived Legacy Scripts

> Status: legacy compatibility notes; do not treat as active tooling contracts.
> Canonical infra docs: [`tools/infra/README.md`](../../../tools/infra/README.md), [`docs/README.md`](../../../docs/README.md).
> Markdown governance: [`docs/MarkdownCorpusGovernance.md`](../../../docs/MarkdownCorpusGovernance.md).

These scripts were removed from the active `scripts` CLI and the maintained
documentation/build pipeline. They are kept only for archaeology, one-off
conversions, or historical comparison work.

Archived here in this cleanup:
- `graph_to_blueprint_inplace.py`
  Old in-place source patcher for `@[blueprint]` tags from the `docs-map` lane.
- `graph_to_blueprint_bulk.py`
  Old bulk `attribute [blueprint] ...` file generator from the `docs-map` lane.
- `auto_tag.py`
  Old bulk blueprint tagger using `docs-map/declarations.json`.
- `generate_library_index.py`
  Old exhaustive LaTeX index generator over `tools.graph` / `docs-map`.
- `agent_doc_gen.py`
  Old local declaration-neighborhood LaTeX stub generator over `tools.graph`.
- `build_theory_manifest.py`
  Old manifest builder over `full_graph.json` / `theory_toc.json`.
- `cluster_theory.py`
  Old Leiden clustering tool over the pre-authoritative `full_graph.json` lane.
- `make_graph.py`
  Old docs-map/module_graph exporter over the archived `InfoGeometry.GraphExport` Lean lane.
- `refactor_plan.py`
  Old deterministic plan generator over `docs-map/module_graph.json`.
- `ci_baseline_docsmap.sh`
  Old CI-style baseline script for the archived docs-map/module_graph lane.

Current replacements:
- declaration DAG: `tools/infra/refresh_decl_graph.py`
- blueprint coverage: `tools/infra/refresh_blueprint_tags.py`
- heavy semantic export: `tools/frontier/semantic_block_export.py`
- frontier analysis: `tools/frontier/skynet_v2.py`
- status/doc refresh: `tools/docs/update_repo_docs.py`

Practical rule:
- do not route new automation through these files
- use them only when you explicitly need legacy behavior for comparison or conversion

## Current Codebase Status

Status pointer refreshed: 2026-04-16 (Europe/Sofia). See [../../../docs/CODEBASE_STATUS.md](../../../docs/CODEBASE_STATUS.md) for the current build/audit state.
