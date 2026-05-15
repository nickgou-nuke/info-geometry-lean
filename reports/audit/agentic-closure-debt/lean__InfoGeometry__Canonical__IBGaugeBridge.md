# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:18.032764+00:00`
Root: `lean/InfoGeometry/Canonical/IBGaugeBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **4**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/IBGaugeBridge.lean` | `advisory` | 13 | 0 | 4 | 5 | 9 |

## Findings by file

### `lean/InfoGeometry/Canonical/IBGaugeBridge.lean`
- module: `InfoGeometry.Canonical.IBGaugeBridge`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L40 [soft] `simp-law-injection` in `simp-declaration ibProjectiveState_normalize_eq_IBGibbs` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L48 [soft] `skeletal-proof` in `theorem IBUnnormalized_shift_eq_smul` — proof appears to close via minimal tactic one-liner
  - L63 [advisory] `local-hypothesis-injection` in `theorem IBUnnormalized_shift_eq_smul` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L64 [advisory] `local-hypothesis-injection` in `theorem IBUnnormalized_shift_eq_smul` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L101 [soft] `skeletal-proof` in `theorem IBUnnormalized_shift_ne_zero` — proof appears to close via minimal tactic one-liner
  - L112 [advisory] `local-hypothesis-injection` in `theorem IBUnnormalized_shift_ne_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L149 [advisory] `local-hypothesis-injection` in `theorem IBGibbs_shift_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L164 [soft] `skeletal-proof` in `theorem IBGibbsMeasure_shift_eq` — proof appears to close via minimal tactic one-liner

