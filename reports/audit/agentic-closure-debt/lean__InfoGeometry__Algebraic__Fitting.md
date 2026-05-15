# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:28.200903+00:00`
Root: `lean/InfoGeometry/Algebraic/Fitting.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **4**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Algebraic/Fitting.lean` | `advisory` | 17 | 0 | 4 | 9 | 13 |

## Findings by file

### `lean/InfoGeometry/Algebraic/Fitting.lean`
- module: `InfoGeometry.Algebraic.Fitting`
- status: `advisory`
- debt_score: `17`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L27 [soft] `skeletal-proof` in `theorem ascent_le` — proof appears to close via minimal tactic one-liner
  - L41 [advisory] `local-hypothesis-injection` in `theorem ascent_le` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L43 [advisory] `local-hypothesis-injection` in `theorem ascent_le` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L47 [soft] `skeletal-proof` in `theorem descent_le` — proof appears to close via minimal tactic one-liner
  - L91 [soft] `skeletal-proof` in `theorem isCompl_ker_pow_range_pow` — proof appears to close via minimal tactic one-liner
  - L100 [advisory] `local-hypothesis-injection` in `theorem isCompl_ker_pow_range_pow` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L107 [advisory] `local-hypothesis-injection` in `theorem isCompl_ker_pow_range_pow` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L118 [advisory] `local-hypothesis-injection` in `theorem isCompl_ker_pow_range_pow` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L122 [advisory] `existential-packaging` in `theorem surjective_on_range` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L128 [advisory] `local-hypothesis-injection` in `theorem surjective_on_range` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L133 [soft] `skeletal-proof` in `theorem injective_on_range` — proof appears to close via minimal tactic one-liner
  - L142 [advisory] `local-hypothesis-injection` in `theorem injective_on_range` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

