# Determinant / Log-Volume / Entropy Topic Map

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This note tracks the scalar determinant and log-volume corridor.

It is a topic map, not a proof summary.

## Current high-confidence files

The current scalar corridor is best read through:

- `lean/InfoGeometry/Canonical/DeterminantCore.lean`
- `lean/InfoGeometry/Canonical/Determinant.lean`
- `lean/InfoGeometry/Canonical/LogDet.lean`
- `lean/InfoGeometry/Jordan/LogDet.lean`
- `lean/InfoGeometry/Canonical/RelativePotentialScalarBridge.lean`
- `lean/InfoGeometry/Canonical/UniversalVolume.lean`
- `lean/InfoGeometry/Canonical/LogSpineBridge.lean`
- `lean/InfoGeometry/Canonical/ZetaDeterminant.lean`
- `lean/InfoGeometry/Thermo/FromLogDet.lean`
- `lean/InfoGeometry/Canonical/ThermoFromLogDet.lean`

## Current reading

The stable scalar story is:

- multiplicative change;
- additive log or log-volume;
- scalar potential or thermodynamic interpretation as downstream packaging.

This should be read as a scalar corridor. It is not yet the missing
support-log owner layer described in
`docs/operator_log_corridor_doctrine.md`.

## Current caution

Do not treat this scalar corridor as if it already provides a native
operator-log owner. That remains a future packet.

## Use rule

Treat this note as a topic map only. Exact ownership belongs to the source
modules above.
