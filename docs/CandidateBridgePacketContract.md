# Candidate Bridge Packet Contract

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This document defines the typed bridge packet for forcing symbolic
correspondences into one of three theorem-level outcomes:

1. `equivalence`
2. `obstruction`
3. `discard`

## Purpose

Many candidate analogies feel structurally right but are mathematically mixed.
This packet forces each candidate map to declare:

- source and target owner surfaces,
- claimed invariant,
- explicit proposed map,
- theorem target if closure is claimed,
- mismatch object if preservation fails,
- or explicit discard reason.

## Paths

- schema: `tools/schema/candidate_bridge_packet.json`
- builder/validator: `tools/infra/candidate_bridge_packet.py`

## Build

```bash
python3 tools/infra/candidate_bridge_packet.py build \
  --out reports/research/bridge-packets/cbp-example.json \
  --source-owner lean/InfoGeometry/Canonical/TomitaTakesaki.lean \
  --target-owner lean/InfoGeometry/Canonical/ModularHamiltonianDoubledBridge.lean \
  --claimed-invariant "modular generator preserved under doubled translation" \
  --map-kind intertwiner \
  --map-expression "Phi : operatorLane -> doubledLane" \
  --outcome-class obstruction \
  --theorem-kind theorem \
  --theorem-name modularHamiltonian_doubled_preservation \
  --mismatch-name projectorMismatch \
  --mismatch-gap "metric support and spectral support do not coincide on the surrogate lane" \
  --unresolved-assumption "unbounded closure remains pending"
```

## Validate

```bash
python3 tools/infra/candidate_bridge_packet.py validate \
  --packet reports/research/bridge-packets/cbp-example.json
```

## Outcome Discipline

- `equivalence`: theorem target is required; mismatch object must be absent.
- `obstruction`: theorem target and mismatch object are required.
- `discard`: discard reason is required.

This keeps symbolic discovery aligned to a strict closure grammar:
equivalence, quantified obstruction, or rejection.
