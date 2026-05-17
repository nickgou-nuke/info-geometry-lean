# Observability

> Status: `repo-owned observability tooling`
> Scope: static graph overlay, wrapper dedup, and audit artifacts for Lean files

This lane is for derived navigation and audit data. It does not prove theorems.
Lean remains proof authority; the overlay is an external analysis surface.

## Current Toolchain

- `graph_overlay_toolchain/graph_overlay/scripts/lean_graph_overlay.py`
  static scanner for Lean sources, alpha-normalized wrapper silhouettes, WL hashes,
  SCC summaries, and dashboard/report generation.
- `auto_tagger.py`
  narrow Lean metadata tagger for exact `OwnerTarget` and `Socket` surfaces.
  It injects `InfoGeometry.Meta.OwnerTarget` / `InfoGeometry.Meta.SocketTarget`
  only when a matching declaration is present, and it normalizes attribute
  stacks so owner-targets stay plain and socket-debt contracts can share a
  combined `@[socket_debt_tag, rep_depth ...]` line.

## Smoke Test

Run from the repository root:

```bash
python3 tools/observability/graph_overlay_toolchain/graph_overlay/scripts/lean_graph_overlay.py . --out-dir /tmp/graph_overlay_smoke
```

Outputs:

- `graph_overlay.json`
- `graph_overlay_report.md`
- `graph_overlay_dashboard.html`

## Auto Tagging

The exact contract tagger is:

```bash
python3 tools/observability/auto_tagger.py --root lean/InfoGeometry --dry-run
python3 tools/observability/auto_tagger.py --root lean/InfoGeometry
```

It targets only the repo's existing `OwnerTarget` and `Socket` naming
conventions and ignores comments/docstring examples.

## Intended Use

- identify repeated wrapper silhouettes
- inspect SCC basins and theorem-graph neighborhoods
- generate a lightweight audit overlay before any Lean-native exporter exists
- bulk-tag the remaining exact owner-target and socket-debt contracts without
  widening the contract surface beyond the repo's existing `OwnerTarget` / `Socket`
  naming conventions

## Boundary

This toolchain is a navigation and audit layer only. It should not be used as proof evidence, and its heuristic hashes are not kernel-accurate de-Bruijn expression hashes.
