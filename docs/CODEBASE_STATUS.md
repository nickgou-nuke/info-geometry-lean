# Codebase Status

Last refreshed: 2026-04-16 (Europe/Sofia)

## Verified Repository Snapshot

- Branch: `main`
- HEAD: `056132a5ce3b4c619c86f9f1eb6c0cedbbb27818`
- Working tree: **dirty** at the time of this snapshot (tracked edits + untracked lanes under `docs/black_books/`, `lean/InfoGeometry/Canonical/`, `lean/InfoGeometry/LLM/`, `leantrail/`, `tools/infra/`)

This file is the maintained operational status surface for external readers who need a concrete build and audit snapshot.

## Verification Gates

### Passing gates (exit code `0`)

1. `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.LLM`
2. `python3 tools/infra/check_gauge_obstruction_tags.py`
3. `python3 tools/quality/functorial_invariance_audit.py --json-out reports/dag/functorial-invariance-audit.json --md-out reports/dag/functorial-invariance-audit.md`
4. `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock --wfail InfoGeometry.Canonical.AQFTOperatorInterface`
5. `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock --wfail InfoGeometry.Canonical.CalabiYauBridge`
6. `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock --wfail InfoGeometry.Canonical.ConformalUnification`
7. `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock --wfail InfoGeometry.Canonical.GrandSynthesis`
8. `python3 tools/infra/module_keyword_theory_program.py --module ... --json-out reports/dag/module-theory-program.json --md-out reports/dag/module-theory-program.md`

`check_gauge_obstruction_tags.py` summary:
- `files_scanned=759`
- `files_with_gaugeObstruction=1`
- `anomaly_bearing=0`
- `declarations_prove_nonzero=0`

`functorial_invariance_audit.py` summary:
- `status=PASS`
- `root_decl_total=1385` (Core/MaxEnt/Convex/Geometry roots)
- `root_with_canopy_total=130`
- `root_tagged_total=1` (from `artifacts/dag/representation-depth-tags.json`)
- `root_untagged_with_canopy_total=129`
- `isomorphism_corridor_total=8`
- `simplex_projective_corridor_total=4`
- explicit corridor witness includes:
  - [`InfoGeometry.Convex.ProjectiveState`](../lean/InfoGeometry/Convex/ProjectiveRays.lean)
    → [`InfoGeometry.Canonical.ProjectiveAlgebraComparison.epsilon_is_mathlib_involute`](../lean/InfoGeometry/Canonical/ProjectiveAlgebraComparison.lean)

`module_keyword_theory_program.py` summary (latest refresh):
- modules analyzed: `4`
- `AQFTOperatorInterface`: decls `55`, reaching roots `1`, roots reached `1`
- `CalabiYauBridge`: decls `25`, reaching roots `24`, roots reached `3`
- `ConformalUnification`: decls `354`, reaching roots `3`, roots reached `1`
- `GrandSynthesis`: decls `19`, reaching roots `1`, roots reached `1`
- literature context + theorem packets written to:
  - [`reports/dag/module-theory-program.md`](../reports/dag/module-theory-program.md)
  - [`reports/dag/module-theory-program.json`](../reports/dag/module-theory-program.json)

### Failing gate (exit code `1`)

3. `/bin/bash -lc "PYTHONPATH=. lake script run strictCheck"`
4. `python3 tools/quality/pauli_seal_audit.py --root lean/InfoGeometry/Canonical --json-out reports/pauli-seal-audit.json`

Failure surface (current):
- strict build remains red under `--wfail` due warning debt in replayed targets
  (unused section vars, unnecessary `simpa`, unused simp args)
- standalone check of [`ProjectorEquivariance.lean`](../lean/InfoGeometry/Canonical/ProjectorEquivariance.lean)
  is currently build-green; treat parser-regression claims as stale unless re-observed.
- high-volume warning contributors in the latest strict replay include:
  deeper canonical lanes (`DrazinSupercharge`, `ModularSuperchargeClosure`)
  seen in `ModularHamiltonianDoubledBridge` dependency builds, with additional
  warning clusters still expected in full strict replay.
- Pauli-seal mandatory gate is red on canonical surface:
  - files scanned: `444`
  - findings: `1474`
  - functorial reconciliation gate: `loaded` (`status=PASS`, `roots_with_canopy=130`, `isomorphism_corridor_total=8`, `simplex_projective_corridor_total=4`)
  - directive counts:
    - `I.no_mask_mandate`: `1006`
    - `II.functorial_connectivity`: `41`
    - legacy `IV.semantic_weight_ratio`: `331` (historical count from the old density heuristic; superseded by `IV.multilingual_bridge_fidelity`)
    - `V.identity_via_reflexivity`: `96`
  - top offending files by finding count:
    - [`BogoliubovTransport.lean`](../lean/InfoGeometry/Canonical/BogoliubovTransport.lean) (`47`)
    - [`ModularSuperchargeClosure.lean`](../lean/InfoGeometry/Canonical/ModularSuperchargeClosure.lean) (`44`)
    - [`TomitaTakesaki.lean`](../lean/InfoGeometry/Canonical/TomitaTakesaki.lean) (`37`)
    - [`DrazinSupercharge.lean`](../lean/InfoGeometry/Canonical/DrazinSupercharge.lean) (`34`)
    - [`EinsteinAnomalyOperator.lean`](../lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean) (`31`)

Recent strict-warning reductions completed in this session:
- [`BoundaryProjector.lean`](../lean/InfoGeometry/Canonical/BoundaryProjector.lean)
- [`CertifiedInverseKernel.lean`](../lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean)
- [`BekensteinBound.lean`](../lean/InfoGeometry/Canonical/BekensteinBound.lean)
- [`AnalyticalIndexCore.lean`](../lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean)
- [`WeylGaugeOperatorLift.lean`](../lean/InfoGeometry/Canonical/WeylGaugeOperatorLift.lean)
- [`GeometricTensorOperatorLift.lean`](../lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean)
- [`BerryConnection.lean`](../lean/InfoGeometry/Canonical/BerryConnection.lean)
- [`RelationalInformationCore.lean`](../lean/InfoGeometry/Canonical/RelationalInformationCore.lean)
- [`RelationalInformationDynamics.lean`](../lean/InfoGeometry/Canonical/RelationalInformationDynamics.lean)
- [`SuperchargeCentralChargeClosure.lean`](../lean/InfoGeometry/Canonical/SuperchargeCentralChargeClosure.lean)
- [`AttentionDiracBridge.lean`](../lean/InfoGeometry/Canonical/AttentionDiracBridge.lean)
- [`DrazinKreinCompatibility.lean`](../lean/InfoGeometry/Canonical/DrazinKreinCompatibility.lean)
- [`CliffordDictionary.lean`](../lean/InfoGeometry/Quantum/CliffordDictionary.lean)
- [`DrazinFredholmBridge.lean`](../lean/InfoGeometry/Canonical/DrazinFredholmBridge.lean)
- [`SplitCliffordHeadPhaseFlip.lean`](../lean/InfoGeometry/Canonical/SplitCliffordHeadPhaseFlip.lean)

## Canonical Status Highlights

- Modular translator/coherence lane is present:
  - [`ModularHamiltonianDoubledBridge.lean`](../lean/InfoGeometry/Canonical/ModularHamiltonianDoubledBridge.lean)
  - [`ModularHamiltonianPregSupportBridge.lean`](../lean/InfoGeometry/Canonical/ModularHamiltonianPregSupportBridge.lean)
- Spectroscopic translator/coherence lane is present:
  - [`SpectroscopicGaugeKMSBridge.lean`](../lean/InfoGeometry/Canonical/SpectroscopicGaugeKMSBridge.lean)
  - [`SpectroscopicGauge.lean`](../lean/InfoGeometry/Canonical/SpectroscopicGauge.lean)
- Path-integral translator lane is present:
  - [`HestenesGibbsPathIntegral.lean`](../lean/InfoGeometry/Canonical/HestenesGibbsPathIntegral.lean)
  - [`DiscreteRouterHestenesPathBridge.lean`](../lean/InfoGeometry/LLM/DiscreteRouterHestenesPathBridge.lean)
- Explicit finite surrogate layer is present:
  - [`ProofSamplingShadow.lean`](../lean/InfoGeometry/LLM/ProofSamplingShadow.lean)
  - [`CompilerRosetta.lean`](../lean/InfoGeometry/LLM/CompilerRosetta.lean)
  - [`CompilerTelemetry.lean`](../lean/InfoGeometry/Meta/CompilerTelemetry.lean)
- Arnold-network presentation translator is present:
  - [`ArnoldNetworkPresentation.lean`](../lean/InfoGeometry/Canonical/ArnoldNetworkPresentation.lean)
- Penrose capstone discharge strengthened (bounded lane):
  - [`OperatorPenroseUnification.lean`](../lean/InfoGeometry/Canonical/OperatorPenroseUnification.lean)
  - constructive junction discharge theorems added
    (`realizedProjectorTomitaIdentification_canonical`,
    `unificationDependencies_of_capstoneWitness`,
    `unificationDependencies_of_closedCapstoneWitness`,
    `operator_penrose_unification_closed`)
- Fierz readout translator hardened:
  - [`FierzReadout.lean`](../lean/InfoGeometry/Canonical/FierzReadout.lean)
  - support/generator moved to explicit `toQuantumPresentationWith` parameters,
    with `toQuantumPresentation` retained as a default wrapper
- SYK two-copy interface discharge strengthened:
  - [`SYKTwoCopyInterface.lean`](../lean/InfoGeometry/Canonical/SYKTwoCopyInterface.lean)
  - added explicit finite protocol witness path
    (`TraversableProtocolWitness`, `traversableProtocolRepoClaim_holds`)
  - owner-anchor theorem claims are now exported as repo-tier `TaggedClaim`s
    (`topologicalIndexZ2_append_owner_claim_holds`,
    `connesCocycle_state_chain_owner_claim_holds`)
- Canonical parse blockers cleared in this session:
  - [`CapstoneSemanticAudit.lean`](../lean/InfoGeometry/Canonical/CapstoneSemanticAudit.lean)
  - [`HestenesRealStructures.lean`](../lean/InfoGeometry/Canonical/HestenesRealStructures.lean)
  - both now parse/build again after `omit ... in` syntax cleanup
- Quantum presentation dependency lane repaired:
  - [`QuantumPresentation.lean`](../lean/InfoGeometry/Canonical/QuantumPresentation.lean)
  - `ℝ` scalar witness surface now imports `Mathlib.Data.Real.Basic`
- Canonical umbrella import is active:
  - [`All.lean`](../lean/InfoGeometry/Canonical/All.lean)
- Canopy assembly surfaces are compile-green under `--wfail` for:
  - [`AQFTOperatorInterface.lean`](../lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean)
  - [`CalabiYauBridge.lean`](../lean/InfoGeometry/Canonical/CalabiYauBridge.lean)
  - [`ConformalUnification.lean`](../lean/InfoGeometry/Canonical/ConformalUnification.lean)
  - [`GrandSynthesis.lean`](../lean/InfoGeometry/Canonical/GrandSynthesis.lean)

## Tooling Status Highlights

- Candidate bridge packet intake lane is present:
  - `tools/schema/candidate_bridge_packet.json`
  - `tools/infra/candidate_bridge_packet.py`
  - [`CandidateBridgePacketContract.md`](CandidateBridgePacketContract.md)
- LeanTrail scaffold is present and still evolving:
  - `leantrail/backend/*`
  - `leantrail/api/*`
  - `leantrail/schemas/*`
  - [`LeanTrail.md`](LeanTrail.md)
  - [`LeanTrailBlueprint.md`](LeanTrailBlueprint.md)
  - memory-carrier adapters:
    - `tools/leantrail/export.py`
    - `tools/leantrail/adapters.py`
    - formats: `graphml`, `neo4j-csv`, `arango-json`
  - conformance gate:
    - `tools/leantrail/conformance.py`
    - `lake script run leantrailConformance ...`
    - validates snapshot parity against external exports/reimports
      (count drift, SCC signature, path parity, hotspot overlap)
  - Arango ingestion lane:
    - `tools/leantrail/arango_ingest.py`
    - `lake script run leantrailArangoIngest ...`
  - Arango physics evaluation lane:
    - `tools/leantrail/arango_physics_evaluator.py`
    - `lake script run leantrailArangoPhysicsEval ...`
    - supports local `ΔS` (baseline/candidate) and live AQL mode
  - failure memory lane:
    - `tools/leantrail/failure_harvester.py`
    - `lake script run leantrailFailureHarvest ...`
    - supports process-flow defects + optional strict/lake build-log ingest
    - `scripts/quality/strict-check.sh` now auto-harvests strict logs on failure
      into `artifacts/leantrail/failed_transitions.jsonl`
  - path bind/lock lane:
    - `tools/leantrail/path_lock_registry.py`
    - `lake script run leantrailPathLock ...`
    - traversal policy support: `any | exclude-failed | locked-only`
  - conformance lock gate:
    - `tools/leantrail/conformance.py --required-locked-paths ...`
    - repo profile file: `leantrail/config/required_locks.json`
  - hole packet lane:
    - `tools/leantrail/hole_packets.py`
    - `lake script run leantrailHolePackets ...`

- Socratic-vs-closure policy split is now explicit:
  - `tools/prompts/SOCRATIC_CLOSURE_PROTOCOL.md`
  - linked in Jungian/Pauli and autotheory handover prompt packs
  - enforced by `tools/infra/agentic_policy_lint.py` text-link checks

Latest adapter conformance checks observed green in this session:
- snapshot vs `graphml`: pass
- snapshot vs `neo4j-csv`: pass
- snapshot vs `arango-json`: pass

## DAG Artifact Snapshot

From `artifacts/dag/index/meta.json`:

- `schemaVersion`: `3`
- `timestamp`: `2026-04-15T22:06:28.722846+00:00`
- `nodeCount`: `17945`
- `edgeCount`: `149817`
- `oleanHash`: `43f327054d34dbf35f81d2319cd264a7f27409ac136f9bcdd5ee0e74d0837ff0`

From `reports/dag/representation-depth-audit.json`:
- status: `PASS`
- depth counts (tracked inventory): `L0=1, L1=5, L2=5, L3=8, L4=1, L5=3`

## Documentation Rule

Use this file as the operational status source for README and other entry docs.
When status changes, update this file first, then README/doc links.

Truth order remains:

1. Lean source under `lean/InfoGeometry/`
2. `lean/InfoGeometry/Audit.lean` and `lean/InfoGeometry/Meta/Architecture.lean`
3. DAG atomic artifacts under `artifacts/dag/`
4. Reports and narrative docs
