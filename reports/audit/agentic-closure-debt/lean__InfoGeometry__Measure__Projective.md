# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:01.523111+00:00`
Root: `lean/InfoGeometry/Measure/Projective.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **4**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Measure/Projective.lean` | `advisory` | 12 | 0 | 4 | 4 | 8 |

## Findings by file

### `lean/InfoGeometry/Measure/Projective.lean`
- module: `InfoGeometry.Measure.Projective`
- status: `advisory`
- debt_score: `12`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L17 [advisory] `existential-packaging` in `def AEAddConst` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L24 [soft] `skeletal-proof` in `lemma AEAddConst.symm` — proof appears to close via minimal tactic one-liner
  - L36 [soft] `skeletal-proof` in `lemma AEAddConst.trans` — proof appears to close via minimal tactic one-liner
  - L59 [advisory] `existential-packaging` in `def SameRay` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L67 [soft] `skeletal-proof` in `lemma SameRay.symm` — proof appears to close via minimal tactic one-liner
  - L71 [advisory] `local-hypothesis-injection` in `lemma SameRay.symm` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L78 [soft] `skeletal-proof` in `lemma SameRay.trans` — proof appears to close via minimal tactic one-liner

