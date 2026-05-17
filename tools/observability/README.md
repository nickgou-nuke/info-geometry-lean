# Observability

> Status: `repo-owned observability tooling`
> Scope: static graph overlay, wrapper dedup, and audit artifacts for Lean files

This lane is for derived navigation and audit data. It does not prove theorems.
Lean remains proof authority; the overlay is an external analysis surface.

## Current Toolchain

- `graph_overlay_toolchain/graph_overlay/scripts/lean_graph_overlay.py`
  static scanner for Lean sources, alpha-normalized wrapper silhouettes, WL hashes,
  SCC summaries, and dashboard/report generation.

## Smoke Test

Run from the repository root:

```bash
python3 tools/observability/graph_overlay_toolchain/graph_overlay/scripts/lean_graph_overlay.py . --out-dir /tmp/graph_overlay_smoke
```

Outputs:

- `graph_overlay.json`
- `graph_overlay_report.md`
- `graph_overlay_dashboard.html`

## Intended Use

- identify repeated wrapper silhouettes
- inspect SCC basins and theorem-graph neighborhoods
- generate a lightweight audit overlay before any Lean-native exporter exists

## Boundary

This toolchain is a navigation and audit layer only. It should not be used as proof evidence, and its heuristic hashes are not kernel-accurate de-Bruijn expression hashes.
