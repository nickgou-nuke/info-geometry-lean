# Canonical Spine Migration

> Status: `generated/historical report`
> Audited: 2026-05-02
> Note: Treat this as a snapshot. Regenerate before relying on it.
> See: [README.md](../README.md), [docs/README.md](../docs/README.md), [docs/CODEBASE_STATUS.md](../docs/CODEBASE_STATUS.md)

This note tracks which existing entry points are already routed through the
canonical relative-geometry spine and which remain pending.

## Migrated

| Existing surface | Canonical spine route | Branch | Status |
| --- | --- | --- | --- |
| `InfoGeometry.Volume.RadonNikodym.HasScalarRNBridge.rn` | `HasScalarRNBridge.toExactBridge -> toLogGenerator` | exact descent | migrated |
| `InfoGeometry.Canonical.Determinant.linearEquivLogGenerator` | `VolumeHom -> logAbsUnitsLinearization -> LogGenerator` | exact descent | migrated |
| `InfoGeometry.Volume.ConnesCocycle.cocycleLogPotential` | `scalarCocycleDefectiveBridge -> scalarCocycleDefectiveLogGenerator` | defective descent | migrated |

## Pending

| Existing surface | Intended canonical route | Branch | Status |
| --- | --- | --- | --- |
| `InfoGeometry.Canonical.TomitaTakesaki` modular Hamiltonian flow | `FunctionalCalculusLinearization -> OperatorLogGenerator -> GeneratedFlow` | operator log branch | pending |
| `InfoGeometry.Canonical.LogDet.logDetBarrier` on SPD | log-generator/potential layer, without forcing SPD multiplication into a false exact monoid story | exact response layer | pending |
| `InfoGeometry.Canonical.BekensteinBound` cocycle consumers | use `scalarCocycleDefectiveLogGenerator` or downstream `GeneratedFlow` wrappers | defective descent consumer | pending |
| synthesis/umbrella modules (`MasterSynthesis`, `GrandSynthesis`, related façades) | replace direct legacy references with thin wrappers over `LogGenerator`/`GeneratedFlow` | mixed | pending |

## Current rule

- Prefer new adapters to destructive rewrites.
- Keep exact, defective, and operator branches separate.
- Treat old public names as acceptable only when they are thin wrappers or clearly marked pending.
- Use the thermodynamic naming conventions in `reports/canonical-thermodynamic-dictionary.md`
  when documenting or refactoring higher-level theory surfaces.
