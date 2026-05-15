# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:42.286819+00:00`
Root: `lean/InfoGeometry/GromovWittenErlangen/CP1DrazinNilpotentCountRayExample.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **1**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/GromovWittenErlangen/CP1DrazinNilpotentCountRayExample.lean` | `advisory` | 6 | 0 | 1 | 4 | 5 |

## Findings by file

### `lean/InfoGeometry/GromovWittenErlangen/CP1DrazinNilpotentCountRayExample.lean`
- module: `InfoGeometry.GromovWittenErlangen.CP1DrazinNilpotentCountRayExample`
- status: `advisory`
- debt_score: `6`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L270 [advisory] `existential-packaging` in `def residueBlocks` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L278 [advisory] `existential-packaging` in `def frobeniusSemisimple` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L285 [advisory] `bridge-shaped-declaration` in `def bridge` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L302 [soft] `skeletal-proof` in `theorem edgeLocalizedDrazinResidue_line` — proof appears to close via minimal tactic one-liner

