# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:46.454428+00:00`
Root: `lean/InfoGeometry/Canonical/BulgarianThermodynamicGeometryBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **0**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/BulgarianThermodynamicGeometryBridge.lean` | `advisory` | 9 | 0 | 0 | 9 | 9 |

## Findings by file

### `lean/InfoGeometry/Canonical/BulgarianThermodynamicGeometryBridge.lean`
- module: `InfoGeometry.Canonical.BulgarianThermodynamicGeometryBridge`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [advisory] `existential-packaging` in `def finiteThermodynamicMoment` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L42 [advisory] `existential-packaging` in `def finiteFisherCovarianceEntry` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L53 [advisory] `existential-packaging` in `def familyAInterfaceOfSouriau` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L94 [advisory] `existential-packaging` in `def familyDInterfaceOfSouriau` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L119 [advisory] `bridge-shaped-declaration` in `theorem familyA_bridge_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L119 [advisory] `existential-packaging` in `theorem familyA_bridge_packet` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L132 [advisory] `bridge-shaped-declaration` in `theorem familyD_bridge_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L132 [advisory] `existential-packaging` in `theorem familyD_bridge_packet` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

