# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:05.088676+00:00`
Root: `lean/InfoGeometry/Canonical/DrazinSpectralProjectorBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **4**
- Hard: **0**
- Soft: **0**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DrazinSpectralProjectorBridge.lean` | `advisory` | 4 | 0 | 0 | 4 | 4 |

## Findings by file

### `lean/InfoGeometry/Canonical/DrazinSpectralProjectorBridge.lean`
- module: `InfoGeometry.Canonical.DrazinSpectralProjectorBridge`
- status: `advisory`
- debt_score: `4`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [advisory] `existential-packaging` in `theorem exists_drazinInverse_with_projector_split_of_zeroIsolatedInSpectrum_finiteAscentDescent` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L64 [advisory] `existential-packaging` in `theorem exists_drazinInverse_with_projector_split_of_zeroIsolatedInSpectrum_package` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L92 [advisory] `existential-packaging` in `theorem exists_drazin_projection_idempotent_of_zeroIsolatedInSpectrum_package` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

