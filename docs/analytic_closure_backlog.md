# Analytic Closure Backlog

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This note tracks the shortest remaining closure path from the current working
state. It is a backlog surface, not an owner authority.

For the executable cleanup sequence, use [CleanupImprovementProgram.md](CleanupImprovementProgram.md).

## Snapshot: `056132a` + Local Working Tree (2026-04-16)

Current reality:

- `InfoGeometry.LLM` builds green under locked build.
- `strictCheck` is red.
- strict debt is currently dominated by warning hygiene under `--wfail`.
- standalone [`ProjectorEquivariance.lean`](../lean/InfoGeometry/Canonical/ProjectorEquivariance.lean)
  currently builds green.

## Recently Settled Surfaces

- Modular doubled translator/coherence lane is active:
  - [`ModularHamiltonianDoubledBridge.lean`](../lean/InfoGeometry/Canonical/ModularHamiltonianDoubledBridge.lean)
  - [`ModularHamiltonianPregSupportBridge.lean`](../lean/InfoGeometry/Canonical/ModularHamiltonianPregSupportBridge.lean)
- Spectroscopic KMS compatibility is explicit and downstream to owner KMS lane:
  - [`SpectroscopicGaugeKMSBridge.lean`](../lean/InfoGeometry/Canonical/SpectroscopicGaugeKMSBridge.lean)
  - [`SpectroscopicGauge.lean`](../lean/InfoGeometry/Canonical/SpectroscopicGauge.lean)
- Path-ensemble translator lane and LLM bridge are wired:
  - [`HestenesGibbsPathIntegral.lean`](../lean/InfoGeometry/Canonical/HestenesGibbsPathIntegral.lean)
  - [`DiscreteRouterHestenesPathBridge.lean`](../lean/InfoGeometry/LLM/DiscreteRouterHestenesPathBridge.lean)

## Active Open Fixtures

1. `strictCheck` warning debt remains high under `--wfail`.
2. lock-contention/noise from overlapping strict runs can obscure gate diagnosis.
3. `OperatorPenroseUnification` is still contract-shaped:
   - five junctions are packaged as assumptions (`UnificationDependencies`),
     not yet discharged end-to-end in-owner.
4. `QuantumPresentation` remains interface-first; most intertwiners are
   structural scaffolds, not deep preservation theorems over concrete owners.
5. Count/projective and corrected phase-space trunks remain adjacent but not
   fully welded by one canonical meeting theorem on the polarized carrier.

## Priority Order

1. Reduce strict `--wfail` debt in high-churn canonical/LLM targets.
2. Enforce single-run lock discipline while running strict gates.
3. Discharge junction contracts in
   [`OperatorPenroseUnification.lean`](../lean/InfoGeometry/Canonical/OperatorPenroseUnification.lean)
   in documented build order.
4. Add one twisted finite-dimensional witness crossing owner -> translator ->
   coherence lanes.
5. Close one explicit count/projective ↔ phase-space welded theorem on shared
   polarized data.

## Corridor View (Isomorphism Pressure)

- **Likely exact corridors** (good candidates for theorem closure):
  - doubled modular generator = Hestenes expression (already theorem-shaped)
  - spectroscopic state compatibility with owned Unruh flow
  - Bayes-router update vs path-Gibbs update (under explicit energy/surprisal match)
- **Likely near-isomorphism corridors** (expect residual terms):
  - projector-response/Weyl anomaly compression
  - finite witness lifts from trunk to capstone
- **High-risk analogy corridors** (keep translator-only until proved):
  - broad Type III global closure rhetoric without affiliated-operator/domain control
  - category/gauge metaphors not yet attached to owner declarations

Use this page as a closure queue, not as a proof certificate.
