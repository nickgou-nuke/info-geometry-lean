# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:45.507186+00:00`
Root: `lean/InfoGeometry/Jordan/LogDet.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **4**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Jordan/LogDet.lean` | `advisory` | 11 | 0 | 4 | 3 | 7 |

## Findings by file

### `lean/InfoGeometry/Jordan/LogDet.lean`
- module: `InfoGeometry.Jordan.LogDet`
- status: `advisory`
- debt_score: `11`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L27 [soft] `simp-law-injection` in `simp-declaration SPD.det_ne_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L40 [advisory] `local-hypothesis-injection` in `lemma normalizedDistortion_det_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L41 [advisory] `local-hypothesis-injection` in `lemma normalizedDistortion_det_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L47 [soft] `skeletal-proof` in `lemma normalizedDistortion_det` — proof appears to close via minimal tactic one-liner
  - L71 [soft] `skeletal-proof` in `lemma logdet_square_nonneg_of_posDef` — proof appears to close via minimal tactic one-liner
  - L93 [soft] `simp-law-injection` in `simp-declaration logDetBregman_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

