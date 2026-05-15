# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:00.157898+00:00`
Root: `lean/InfoGeometry/Canonical/DiracMetricCompatibility.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **2**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DiracMetricCompatibility.lean` | `advisory` | 10 | 0 | 2 | 6 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/DiracMetricCompatibility.lean`
- module: `InfoGeometry.Canonical.DiracMetricCompatibility`
- status: `advisory`
- debt_score: `10`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L22 [soft] `law-field-locker` in `structure-field DiracMetricCompatibility.dirac_sq_eq_metric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L126 [advisory] `local-hypothesis-injection` in `theorem eq_canonicalDiracOfMetric_of_isPositive_of_sq_eq_metric` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L128 [advisory] `local-hypothesis-injection` in `theorem eq_canonicalDiracOfMetric_of_isPositive_of_sq_eq_metric` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L130 [advisory] `local-hypothesis-injection` in `theorem eq_canonicalDiracOfMetric_of_isPositive_of_sq_eq_metric` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L144 [advisory] `local-hypothesis-injection` in `theorem eq_canonicalDiracOfMetric_of_isPositive_of_sq_eq_metric` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L179 [soft] `skeletal-proof` in `lemma inner_dirac_sq` — proof appears to close via minimal tactic one-liner
  - L186 [advisory] `local-hypothesis-injection` in `lemma inner_dirac_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

