# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:04.960531+00:00`
Root: `lean/InfoGeometry/Canonical/DrazinSpectralBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **5**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DrazinSpectralBridge.lean` | `advisory` | 13 | 0 | 5 | 3 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/DrazinSpectralBridge.lean`
- module: `InfoGeometry.Canonical.DrazinSpectralBridge`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L45 [soft] `skeletal-proof` in `theorem HasFiniteAscentDescentAtZero_of_zeroIsolatedInSpectrum_eq` — proof appears to close via minimal tactic one-liner
  - L73 [soft] `skeletal-proof` in `theorem DrazinInfiniteAssumptions_of_zeroIsolatedInSpectrum_finite_ascent_descent` — proof appears to close via minimal tactic one-liner
  - L86 [soft] `skeletal-proof` in `theorem DrazinInfiniteAssumptions_of_zeroIsolatedInSpectrum_zero_isolated` — proof appears to close via minimal tactic one-liner
  - L99 [soft] `skeletal-proof` in `theorem DrazinInfiniteAssumptions_of_zeroIsolatedInSpectrum_classical` — proof appears to close via minimal tactic one-liner
  - L112 [soft] `skeletal-proof` in `theorem DrazinInfiniteAssumptions_of_zeroIsolatedInSpectrum_generalized` — proof appears to close via minimal tactic one-liner
  - L126 [advisory] `existential-packaging` in `theorem exists_drazinInverse_of_zeroIsolatedInSpectrum_finiteAscentDescent` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L138 [advisory] `existential-packaging` in `theorem exists_drazinInverse_of_zeroIsolatedInSpectrum_package` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

