# Major restore and refactor plan

Goal: recover incidentally lost Lean fragments from archives/chats/memory/backups into sandbox-only artifacts, then promote only reviewed, kernel-checked slices later. No live owner file is overwritten in this phase.

Recovery sources audited:
- `agent_writes_recovery_v4/lean/` for exact-path owner snapshots
- `agent_memory_recovery/` for basename snapshots and `untracked_lean/`
- `agent_memory_recovery_stitched/` for stitched reconstructions
- Hermes/Codex/Pi/Antigravity transcripts already verified as additional archive sources

Core rules:
1. sandbox-first only; do not overwrite live owners
2. for each fragment, find its nearest live owner/import corridor before rewriting
3. keep Lean files small and split into reusable helper lemmas
4. only promote exact theorem-safe packets later

## Slice A: high-confidence exact-path restores/refactors

These already have exact-path recovery snapshots and clear live owner paths:
- `lean/InfoGeometry/Physics/HadjiivanovBostConnesBridge.lean`
- `lean/InfoGeometry/Physics/BostConnesGNS.lean`
- `lean/InfoGeometry/Kaehler/FubiniStudyAsymptotics.lean`
- `lean/InfoGeometry/Kaehler/PoincareMetric.lean`
- `lean/InfoGeometry/Information/DeRhamScore.lean`
- `lean/InfoGeometry/Potential/LogPotential.lean`
- `lean/InfoGeometry/Categorical/InfinityTopos.lean`
- `lean/InfoGeometry/Kaehler/AmbroseSinger.lean`
- `lean/InfoGeometry/Topology/MobiusGeometry.lean`

For each file in Slice A:
- read live owner
- read exact-path recovery snapshot
- read nearest importers/usages
- write a sandbox refactor file with smaller helper lemmas and explicit comments about theorem scope
- compile the sandbox file if possible
- record whether the live file is merely duplicated, genuinely weaker, or corrupted

## Slice B: basename-only owner-path audit

These have recovered content but need owner-path confirmation from repo imports/usages:
- `AmplituhedronBoundary.lean`
- `AmplituhedronZetaEquivalence.lean`
- `AnomalyTubuleStability.lean`
- `ArithmeticErlangenSquareRootBridge.lean`
- `CartanInfinitesimalExponentialBridge.lean`
- `ChiralDiracHomologyBridge.lean`
- `CliffordBraidingInterfaces.lean`
- `CliffordBraidingTheorem.lean`
- `ConformalCyclicCosmology.lean`
- `CuntzChiralMomentum.lean`
- `CuntzChiralProjectors.lean`
- `CuntzKMSState.lean`
- `CuntzLorentzPoincarePresentation.lean`
- `FiveGradedTKK.lean`
- `HorizonAttractorMicrostateLedger.lean`
- `HorizonZitterModes.lean`
- `OperatorialJonesCalculus.lean`
- `PrimonZeta.lean`
- `ProjectivePrimePartition.lean`
- `SplitOctonionFibration.lean`
- `VirasoroAlgebra.lean`

For each file in Slice B:
- search repo-wide for imports/usages/symbol matches
- determine whether the recovered file belongs under an existing owner corridor
- write only sandbox placements until an owner-path audit is complete

## Immediate next implementation slice

1. Stage sandbox refactor for `HadjiivanovBostConnesBridge` using the existing `HadjiivanovCuntzBridge` owner and `standardLogBlock_trace`.
2. Audit whether `BostConnesGNS` should remain as-is or be split into smaller helper lemmas in sandbox.
3. Audit `PoincareMetric` against `Geometry/BilingualPoincareMetric.lean` before any rewrite.
4. Audit `DeRhamScore` and `LogPotential` against their importer corridors to determine whether the recovered file is still owner-authoritative or has been superseded.

Artifacts generated in this phase:
- `sandbox/restore_gap_table.md`
- `sandbox/restore_gap_table.json`
- this plan file
