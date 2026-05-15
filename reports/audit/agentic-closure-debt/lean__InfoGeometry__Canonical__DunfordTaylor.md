# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:06.254467+00:00`
Root: `lean/InfoGeometry/Canonical/DunfordTaylor.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **16**
- Hard: **0**
- Soft: **13**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DunfordTaylor.lean` | `advisory` | 29 | 0 | 13 | 3 | 16 |

## Findings by file

### `lean/InfoGeometry/Canonical/DunfordTaylor.lean`
- module: `InfoGeometry.Canonical.DunfordTaylor`
- status: `advisory`
- debt_score: `29`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L45 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L74 [soft] `simp-law-injection` in `simp-declaration mem_resolventSet_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L76 [soft] `skeletal-proof` in `theorem mem_resolventSet_iff` — proof appears to close via minimal tactic one-liner
  - L79 [soft] `skeletal-proof` in `theorem isOpen_resolventSet` — proof appears to close via minimal tactic one-liner
  - L108 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L124 [soft] `simp-law-injection` in `simp-declaration dunfordTaylorIntegral_zero_function` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L126 [soft] `skeletal-proof` in `theorem dunfordTaylorIntegral_zero_function` — proof appears to close via minimal tactic one-liner
  - L132 [soft] `simp-law-injection` in `simp-declaration dunfordTaylorIntegral_const_contour` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L134 [soft] `skeletal-proof` in `theorem dunfordTaylorIntegral_const_contour` — proof appears to close via minimal tactic one-liner
  - L149 [soft] `simp-law-injection` in `simp-declaration rieszProjection_const_contour` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L151 [soft] `skeletal-proof` in `theorem rieszProjection_const_contour` — proof appears to close via minimal tactic one-liner
  - L170 [soft] `simp-law-injection` in `simp-declaration kolihaDrazinInverse_const_contour` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L172 [soft] `skeletal-proof` in `theorem kolihaDrazinInverse_const_contour` — proof appears to close via minimal tactic one-liner
  - L214 [soft] `skeletal-proof` in `theorem idempotentStatement_const_contour` — proof appears to close via minimal tactic one-liner
  - L224 [soft] `skeletal-proof` in `theorem rangeInvariantStatement_const_contour` — proof appears to close via minimal tactic one-liner

