# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:10.563001+00:00`
Root: `lean/InfoGeometry/Canonical/WeylA2ProductDivisibilityShadow.lean`
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
| `lean/InfoGeometry/Canonical/WeylA2ProductDivisibilityShadow.lean` | `advisory` | 13 | 0 | 4 | 5 | 9 |

## Findings by file

### `lean/InfoGeometry/Canonical/WeylA2ProductDivisibilityShadow.lean`
- module: `InfoGeometry.Canonical.WeylA2ProductDivisibilityShadow`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L38 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L62 [soft] `skeletal-proof` in `theorem denominatorA_dvd_numerator` — proof appears to close via minimal tactic one-liner
  - L76 [soft] `skeletal-proof` in `theorem denominatorB_dvd_numerator` — proof appears to close via minimal tactic one-liner
  - L90 [soft] `skeletal-proof` in `theorem denominatorC_dvd_numerator` — proof appears to close via minimal tactic one-liner
  - L109 [soft] `skeletal-proof` in `theorem denominator_dvd_numerator` — proof appears to close via minimal tactic one-liner
  - L130 [advisory] `existential-packaging` in `theorem exists_quotient` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L137 [advisory] `bridge-shaped-declaration` in `theorem product_divisibility_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L137 [advisory] `existential-packaging` in `theorem product_divisibility_packet` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

