# Codebase Cleanup And Improvement Program

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

Last updated: 2026-04-16 (Europe/Sofia)

This is the execution program for cleanup and improvement. It turns the current
closure analysis into sequenced work with explicit gates.

## Evidence Base

Use these as inputs before changing priority:

1. [CODEBASE_STATUS.md](CODEBASE_STATUS.md)
2. [ModuleMap.md](ModuleMap.md)
3. [OperationalIntent.md](OperationalIntent.md)
4. [Theory.md](Theory.md)
5. [analytic_closure_backlog.md](analytic_closure_backlog.md)
6. [../reports/dag/module-theory-program.md](../reports/dag/module-theory-program.md)

Current validated signals:

- `InfoGeometry.LLM` builds under locked build.
- `InfoGeometry.Canonical.ProjectorEquivariance` builds under locked build.
- `strictCheck` remains red under `--wfail` because warning debt is still high.
- `check_gauge_obstruction_tags.py` is green (`files_with_gaugeObstruction=1`, `anomaly_bearing=0`).
- LeanTrail adapter conformance is green for:
  - snapshot vs GraphML
  - snapshot vs Neo4j CSV
  - snapshot vs Arango JSON
- Pauli-seal gate is now mandatory in surrogate audit:
  `tools/quality/pauli_seal_audit.py`.
- Functorial invariance and core-isomorphism tracing gate is now mandatory:
  `tools/quality/functorial_invariance_audit.py`.

Current strict-warning frontier (post latest cleanup pass):

- Reduced/cleaned cluster:
  `BoundaryProjector`, `CertifiedInverseKernel`, `BekensteinBound`,
  `AnalyticalIndexCore`, `WeylGaugeOperatorLift`,
  `GeometricTensorOperatorLift`, `BerryConnection`,
  `RelationalInformationCore`, `RelationalInformationDynamics`,
  `SuperchargeCentralChargeClosure`, `AttentionDiracBridge`,
  `DrazinKreinCompatibility`, `CliffordDictionary`,
  `DrazinFredholmBridge`, `SplitCliffordHeadPhaseFlip`.
- Next blocking cluster to run in W2:
  large warning packs in `DrazinSupercharge` and
  `ModularSuperchargeClosure`, then next strict replay contributors
  surfaced under `--wfail`.

## Program Goals

1. Make strict gates deterministic and green.
2. Convert assumption-packaged capstone contracts into theorem-level closures.
3. Weld adjacent trunks with explicit bridge theorems and one finite witness.
4. Demote analogy rhetoric into either theorem, quantified obstruction, or discard.

## Workstreams

### W0. Pauli Seal Enforcement (Mandatory)

Target:
- block agentic Native Closure Mandated: Prohibited Cheating surfaces on canonical modules by mandatory machine gate.

Actions:
1. Enforce `I.no_mask_mandate` (physically loaded names must be grounded).
2. Enforce `II.functorial_connectivity` (no floating import-only canonical modules).
3. Enforce `III.axiom_surface_seal` (no `sorry`/`admit`/`axiom` holes).
4. Enforce `IV.multilingual_bridge_fidelity` (bridge-bearing prose is preserved; only unsupported or non-bridge rhetoric is rejected).
5. Enforce `V.identity_via_reflexivity` (no grand unity via trivial `rfl`).
6. Keep this gate mandatory in `scripts/audit_surrogates.sh`.

Exit criteria:
1. `python3 tools/quality/pauli_seal_audit.py --root lean/InfoGeometry` exits `0`.

### W1. Gate Stabilization

Target:
- eliminate lock contention noise and keep one strict runner at a time.

Actions:
1. Run only one `strictCheck` process at once.
2. Use locked wrappers for all umbrella/module builds.
3. Record latest gate outcome in [CODEBASE_STATUS.md](CODEBASE_STATUS.md).

Exit criteria:
1. No overlapping `strictCheck`/`run_locked_lake_build` sessions during audit.
2. Reproducible gate outcomes across two consecutive runs.

### W2. Strict Warning Debt Reduction

Target:
- reduce warning debt until `strictCheck` passes.

Actions:
1. Triage warnings by class:
   - unused section vars,
   - unnecessary `simpa`,
   - unused simp args.
2. Fix high-churn canonical and LLM files first.
3. Re-run strict gate after each warning cluster fix.

Exit criteria:
1. `/bin/bash -lc "PYTHONPATH=. lake script run strictCheck"` exits `0`.

### W3. Capstone Contract Discharge

Target:
- discharge the five typed junction contracts in
  [OperatorPenroseUnification.lean](../lean/InfoGeometry/Canonical/OperatorPenroseUnification.lean).

Actions:
1. Replace assumption-only package use with concrete bridge lemmas in build order.
2. Keep owner/translator/coherence roles explicit per file.
3. Validate each discharged junction with locked module builds.

Exit criteria:
1. Junction contracts are theorem-backed on owner data, not only packaged assumptions.

### W4. Trunk Welding And Witness

Target:
- close one explicit meeting theorem between count/projective and corrected phase-space trunks,
  plus one twisted finite-dimensional end-to-end witness.

Actions:
1. Add explicit polarized-carrier weld theorem.
2. Add one finite model with nontrivial twist crossing owner -> translator -> coherence lanes.
3. Confirm import path from canonical umbrella remains healthy.

Exit criteria:
1. Weld theorem and witness compile and are referenced in [ModuleMap.md](ModuleMap.md).

### W5. Isomorphism Corridor Governance

Target:
- enforce a strict classification pipeline for analogy corridors.

Actions:
1. For each corridor, classify as:
   - exact bridge candidate,
   - near-isomorphism (obstruction-carrying),
   - analogy-only (quarantine).
2. Route exact/near candidates through
   [CandidateBridgePacketContract.md](CandidateBridgePacketContract.md).
3. Keep analogy-only lanes out of closure claims.

Exit criteria:
1. Every promoted corridor has either:
   - a theorem-level bridge, or
   - an explicit mismatch/obstruction object.

### W6. Memory-Carrier Governance

Target:
- keep external graph/database memory carriers truthful to canonical LeanTrail snapshots.

Actions:
1. Export adapters via `lake script run leantrailExport --to all`.
2. Run conformance gate for GraphML, Neo4j CSV, and Arango JSON against canonical snapshot.
3. Block ingestion/use of any external carrier when conformance fails.

Exit criteria:
1. All adapter conformance gates are green with `--fail-on-violation`.
2. Latest green reports are present under `artifacts/leantrail/conformance_*.json`.

### W7. Module-Keyword Theory Derivation

Target:
- derive module-local theorem targets from keyword context, full-repo search,
  and trunk→root dependency traces.

Actions:
1. Run `module_keyword_theory_program.py` on the active canonical module set.
2. Validate candidate declarations against owner/translator/coherence roles.
3. Promote only non-vacuous theorem packets into canonical closure queue.

Exit criteria:
1. `reports/dag/module-theory-program.md` is refreshed and linked from README/docs.
2. Each promoted module has at least one trunk→root path witness and one
   concrete theorem packet candidate.

### W8. Not-Even-Wrong Derivation Closure

Target:
- discharge the remaining assumption-heavy junctions documented in
  [RigorousDerivationQueue.md](RigorousDerivationQueue.md).

Actions:
1. Replace raw commutation assumption consumption in winding closure with a
   derived symmetry-to-commutation theorem path.
2. Add a theorem-level Drazin/Weyl compatibility bridge using the constructive
   Riesz/Drazin package.
3. Replace `RouterDefectBridge.residual_eq_observerDefect` assumption-only
   usage with a limit/closure theorem-backed constructor.

Exit criteria:
1. Queue items A/B/C in `RigorousDerivationQueue.md` are marked closed with
   theorem anchors.
2. No new bridge theorem consumes the previous raw assumptions without a
   derivation witness.

## Command Loop

Use this minimal loop:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Canonical.ProjectorEquivariance
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.LLM
python3 tools/infra/check_gauge_obstruction_tags.py
python3 tools/quality/functorial_invariance_audit.py --json-out reports/dag/functorial-invariance-audit.json --md-out reports/dag/functorial-invariance-audit.md
python3 tools/quality/check_translation_registry.py \
  --registry docs/OperatorTheoremTranslationRegistry.md \
  --required-anchor InfoGeometry.Canonical.ModularSuperchargeClosure.superHamiltonian_eq_modularTransportGenerator_lorentzBivectorSeed \
  --required-anchor InfoGeometry.Canonical.ModularSuperchargeClosure.operatorialKMSCondition_lorentzBivectorSeed_of_structural \
  --required-anchor InfoGeometry.Canonical.ModularSuperchargeClosure.exists_lorentzBivectorGenerator_split_with_drazin_lane_centrality \
  --required-anchor InfoGeometry.Canonical.ModularSuperchargeClosure.projectedEvenGenerator_fixed_under_lorentzChiralConeOrbit \
  --required-anchor InfoGeometry.Canonical.ModularSuperchargeClosure.projectedEvenGenerator_fixed_under_lorentzWedgeOrbit \
  --required-anchor InfoGeometry.Canonical.KKTCore.uPlus_eq_gOnePart \
  --required-anchor InfoGeometry.Canonical.KKTCore.uPlus_mul_uPlus_eq_zero \
  --required-anchor InfoGeometry.Canonical.KKTCore.commutator_uPlus_uMinus_isGZero
python3 tools/quality/pauli_seal_audit.py --root lean/InfoGeometry --json-out reports/pauli-seal-audit.json
python3 tools/infra/module_keyword_theory_program.py --module InfoGeometry.Canonical.AQFTOperatorInterface --module InfoGeometry.Canonical.CalabiYauBridge --module InfoGeometry.Canonical.ConformalUnification --module InfoGeometry.Canonical.GrandSynthesis --json-out reports/dag/module-theory-program.json --md-out reports/dag/module-theory-program.md
/bin/bash -lc "PYTHONPATH=. lake script run strictCheck"
```

If strict stays red, continue W2 before opening new theorem branches.

## Completion Definition

Program complete when all hold:

1. strict gate is green (`strictCheck == 0`);
2. capstone dependency contracts are theorem-discharged;
3. one explicit trunk weld theorem is in canonical lane;
4. one twisted finite witness is in canonical lane;
5. corridor registry contains only theorem-backed or obstruction-quantified promotions.
