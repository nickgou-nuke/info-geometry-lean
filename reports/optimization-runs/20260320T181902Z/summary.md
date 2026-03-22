# Optimization Cycle

- run id: `20260320T181902Z`
- git head: `adab8a2a5f4d0411983df7193afb8bdf7c9c487f`
- branch: `auto-opt/dry-cycle-20260320T181902Z`
- worktree: `/tmp/info-geometry-autoopt/20260320T181902Z`
- worktree mode: `created-fresh`
- frontier source: `/home/goutev/LEAN4/info-geometry-lean/reports/dag/skynet-v2-frontier-reverse.json`
- walk: `reverse`
- selected stable id: `block:3117-3498`
- selected source file: `file:///home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/KK/KasparovCycle.lean`

## Selected declarations
- `InfoGeometry.KK.index_bridge_spectral`

## Selected candidate
- ordinal: `1`
- name: `ReviewedCandidate.index_bridge_spectral_constant_family`
- risk: `low`
- packet: `/home/goutev/LEAN4/info-geometry-lean/skills/info-geometry-repo/references/bridge-reviewed-candidates.md`
- review verdict: `accept`
- quarantine recommendation: `yes`
- reviewed materialization sketch: `yes`

### Proof ingredients
- ``InfoGeometry.KK.index_bridge_spectral``
- ``lean/InfoGeometry/KK/KasparovCycle.lean``
- ``InfoGeometry.Canonical.AnalyticalIndex.IndexInvariantAlong``

## Top frontier context
- `InfoGeometry.KK.index_bridge_spectral`
- `InfoGeometry.Canonical.GrandSynthesis.kk_analyticalIndex_eq_of_modularCliffordTransport_state_hypotheses`
- `InfoGeometry.Canonical.GrandSynthesis.kk_analyticalIndex_eq_of_conjugacy_state_hypotheses`
- `InfoGeometry.Canonical.AnalyticalIndex.chiralSliceIsoAlong_of_noZeroEigenCrossing`
- `InfoGeometry.Canonical.AnalyticalIndex.sinkhornRicciIndexInvariant_of_conjugacy_state_hypotheses`

## Hydration
- copied packages: `True`
- copied build cache: `True`

## Targeted build
- run status: `targeted_build_failed`
- build status: `targeted_build_failed`
- materialization status: `materialized`
- module: `InfoGeometry.Unstable.AutoOptCycle`
- quarantine file: `lean/InfoGeometry/Unstable/AutoOptCycle.lean`
- return code: `1`
- stdout: `/home/goutev/LEAN4/info-geometry-lean/reports/optimization-runs/20260320T181902Z/targeted-build-2.stdout.log`
- stderr: `/home/goutev/LEAN4/info-geometry-lean/reports/optimization-runs/20260320T181902Z/targeted-build-2.stderr.log`

## Proof Attempts
- attempt `1` build return code: `1`
  materialization status: `materialized`
  proof command return code: `0`
  proof report: `/home/goutev/LEAN4/info-geometry-lean/reports/optimization-runs/20260320T181902Z/proof-attempt-1.context.report.md`
  proof report verdict: `materialized`
- attempt `2` build return code: `1`
  materialization status: `already_present`
  proof command return code: `0`
  proof report: `/home/goutev/LEAN4/info-geometry-lean/reports/optimization-runs/20260320T181902Z/proof-attempt-2.context.report.md`
  proof report verdict: `already-present`
