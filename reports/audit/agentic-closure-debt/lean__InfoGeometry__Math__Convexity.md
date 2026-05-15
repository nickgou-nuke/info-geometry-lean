# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:59.303891+00:00`
Root: `lean/InfoGeometry/Math/Convexity.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **2**
- Advisory: **11**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Math/Convexity.lean` | `advisory` | 15 | 0 | 2 | 11 | 13 |

## Findings by file

### `lean/InfoGeometry/Math/Convexity.lean`
- module: `InfoGeometry.Math.Convexity`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L24 [soft] `skeletal-proof` in `theorem neg_log_jensen_sum` — proof appears to close via minimal tactic one-liner
  - L42 [advisory] `existential-packaging` in `theorem kl_convexity_finite` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L42 [soft] `skeletal-proof` in `theorem kl_convexity_finite` — proof appears to close via minimal tactic one-liner
  - L57 [advisory] `local-hypothesis-injection` in `theorem kl_convexity_finite` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L59 [advisory] `local-hypothesis-injection` in `theorem kl_convexity_finite` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L62 [advisory] `local-hypothesis-injection` in `theorem kl_convexity_finite` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L64 [advisory] `local-hypothesis-injection` in `theorem kl_convexity_finite` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L67 [advisory] `local-hypothesis-injection` in `theorem kl_convexity_finite` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L68 [advisory] `local-hypothesis-injection` in `theorem kl_convexity_finite` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L74 [advisory] `local-hypothesis-injection` in `theorem kl_convexity_finite` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L78 [advisory] `local-hypothesis-injection` in `theorem kl_convexity_finite` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L81 [advisory] `local-hypothesis-injection` in `theorem kl_convexity_finite` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

