# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:46.988563+00:00`
Root: `lean/InfoGeometry/Canonical/QuasilatticeDirac.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **2**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/QuasilatticeDirac.lean` | `advisory` | 8 | 0 | 2 | 4 | 6 |

## Findings by file

### `lean/InfoGeometry/Canonical/QuasilatticeDirac.lean`
- module: `InfoGeometry.Canonical.QuasilatticeDirac`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L23 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L25 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L41 [soft] `simp-law-injection` in `simp-declaration quasilatticeDirac_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L47 [soft] `skeletal-proof` in `theorem deriv_quasilatticeDirac` — proof appears to close via minimal tactic one-liner
  - L183 [advisory] `local-hypothesis-injection` in `theorem deriv2_quasilatticeDirac_at_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

