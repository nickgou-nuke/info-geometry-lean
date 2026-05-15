# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:06.837239+00:00`
Root: `lean/InfoGeometry/Canonical/EmpiricalChecks.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **3**
- Hard: **0**
- Soft: **1**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/EmpiricalChecks.lean` | `advisory` | 4 | 0 | 1 | 2 | 3 |

## Findings by file

### `lean/InfoGeometry/Canonical/EmpiricalChecks.lean`
- module: `InfoGeometry.Canonical.EmpiricalChecks`
- status: `advisory`
- debt_score: `4`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L44 [advisory] `existential-packaging` in `lemma twoState_freeEnergy_identity_unit` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L44 [soft] `skeletal-proof` in `lemma twoState_freeEnergy_identity_unit` — proof appears to close via minimal tactic one-liner

