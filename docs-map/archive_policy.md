# Archive Policy

## Decision

`InfoGeometry.Archive.Drafts.*` is excluded from release gating.

The canonical release surface is defined by:

- `InfoGeometry`
- `InfoGeometry.Library`
- `InfoGeometry.Canonical.All`

Any non-buildable module outside `InfoGeometry.Archive.Drafts.*` is a CI failure.

## Salvage Workflow (Incremental)

For each draft file:

1. Extract one buildable theorem/definition at a time into a canonical or domain module.
2. Keep the extracted declaration name stable under `InfoGeometry.Canonical.*` (or approved domain path).
3. Add compatibility alias only if needed by in-tree imports.
4. Re-run:
   - `lake build`
   - `python3 -m scripts make-graph --probe-unresolved --out docs-map/graph.json`
   - `python3 -m scripts refactor-plan --module-graph docs-map/module_graph.json --errors .artifacts/nonbuildable_errors.json --out docs-map/refactor_plan.md`
5. Remove salvaged code from the draft file once the canonical declaration is verified.

## Exit Criteria for Removing Draft Exclusion

- `docs-map/module_graph.json` reports `non_buildable = 0`, or
- remaining non-buildable modules are intentionally marked and moved outside the package.
