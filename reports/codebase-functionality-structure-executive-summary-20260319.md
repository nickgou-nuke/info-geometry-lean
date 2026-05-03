# Codebase Functionality and Structure: Executive Summary (2026-03-19)

> Status: `generated/historical report`
> Audited: 2026-05-02
> Note: Treat this as a snapshot. Regenerate before relying on it.
> See: [README.md](../README.md), [docs/README.md](../docs/README.md), [docs/CODEBASE_STATUS.md](../docs/CODEBASE_STATUS.md)

## Purpose
This note is a short companion to the detailed local audit:

- reports/codebase-functionality-structure-audit-20260319.md

It captures the current repository shape, operational paths, and top structural risks in one page.

## One-Page Snapshot

- The repository is dual-purpose: a Lean theorem library plus a self-analysis DAG/semantic-export stack.
- The active publication route is centered on lean/InfoGeometry, especially lean/InfoGeometry/Canonical.
- The active analysis/tooling route is centered on lean/DAG, lean/scripts/DAG/Exploration, and tools/*.py.
- New onboarding docs now provide a clear current-vs-legacy path:
  - README.md
  - NEWCOMER_PATH.md
  - archive/README.md
  - archive/legacy/README.md

## Verified Architecture

### Publication surface

1. lean/InfoGeometry.lean
2. lean/InfoGeometry/Library.lean
3. lean/InfoGeometry/Canonical/All.lean

This establishes a stable umbrella while retaining support for generated extensions.

### Tooling surface

- DAG kernel and analysis: lean/DAG
- Lean wrappers for report/export flows: lean/scripts/DAG/Exploration
- Trusted heavy-module semantic export: tools/semantic_block_export.py
- Frontier exploration: tools/skynet_v2.py
- Auto status/doc refresh: tools/generate_auto_docs.py and tools/update_repo_docs.py

## Quantitative Signals (Current Snapshot)

- Lean files under lean/InfoGeometry: 372
- Lean files under lean/InfoGeometry/Canonical: 164
- Lean files under lean/DAG: 31
- Quarantine manifest entries: 35

docs-map/module_graph.json snapshot:

- discovered modules: 227
- nodes: 227
- import edges: 520
- buildable: 197
- non-buildable: 30
- connected components: 5
- largest component: 223

## Stable vs Quarantine Boundary

- Explicit quarantine registry: scripts/quality/quarantine_manifest.txt
- Quarantine umbrella import surface: lean/InfoGeometry/Unstable/Quarantine.lean
- Enforcement controls:
  - .github/workflows/ci.yml
  - scripts/enforce_quarantine_imports.sh
  - scripts/audit_surrogates.sh

Observed import scan in this snapshot shows InfoGeometry.Unstable.* imports only inside the quarantine umbrella.

## Coupling Highlights

High-frequency canonical imports indicate practical coupling anchors around:

- SpectralInference
- HessianGeometry
- Drazin
- TomitaTakesaki
- MoorePenrose
- ConformalUnification
- RicciMongeAmpere

Interpretation: these modules act as bridge hubs and change-amplifiers for downstream files.

## Main Risks

1. Canonical breadth risk: 164 canonical files increase blast radius for cross-cutting edits.
2. Quarantine debt remains material: 35 modules are still explicitly segregated.
3. Graph snapshot shows 30 non-buildable modules and should be tracked over time.
4. Generated/untracked analysis artifacts require disciplined regeneration and should not become hand-edited sources.

## Recommended Near-Term Actions

1. Keep newcomer path and archive guidance current as the first onboarding surface.
2. Track non-buildable module count trend from docs-map/module_graph.json in periodic audits.
3. Prioritize quarantine-reduction roadmap by bridge-hub impact (start with modules that feed canonical synthesis layers).
4. Add a lightweight recurring report for coupling hotspots (top import fan-in and fan-out deltas).

## Reference

For full details and evidence trail, use:

- reports/codebase-functionality-structure-audit-20260319.md
