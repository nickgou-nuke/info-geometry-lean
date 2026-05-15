# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:41.730413+00:00`
Root: `lean/InfoGeometry/GrandUnification/SpectralThermalNormalization.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **4**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/GrandUnification/SpectralThermalNormalization.lean` | `advisory` | 10 | 0 | 4 | 2 | 6 |

## Findings by file

### `lean/InfoGeometry/GrandUnification/SpectralThermalNormalization.lean`
- module: `InfoGeometry.GrandUnification.SpectralThermalNormalization`
- status: `advisory`
- debt_score: `10`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L65 [soft] `law-field-locker` in `structure-field SpectralThermalNormalizationPacket.beta_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field SpectralThermalNormalizationPacket.energy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L69 [soft] `law-field-locker` in `structure-field SpectralThermalNormalizationPacket.boltzmannPotential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L78 [soft] `law-field-locker` in `structure-field SpectralThermalNormalizationPacket.partition_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L268 [advisory] `existential-packaging` in `def SpectralThermalNormalizationTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

