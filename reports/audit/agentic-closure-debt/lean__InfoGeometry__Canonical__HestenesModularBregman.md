# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:14.472187+00:00`
Root: `lean/InfoGeometry/Canonical/HestenesModularBregman.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **12**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/HestenesModularBregman.lean` | `advisory` | 27 | 0 | 12 | 3 | 15 |

## Findings by file

### `lean/InfoGeometry/Canonical/HestenesModularBregman.lean`
- module: `InfoGeometry.Canonical.HestenesModularBregman`
- status: `advisory`
- debt_score: `27`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L48 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L50 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L71 [soft] `skeletal-proof` in `theorem modularIdentity_eq_id` — proof appears to close via minimal tactic one-liner
  - L86 [soft] `skeletal-proof` in `theorem modularDeviation_identity` — proof appears to close via minimal tactic one-liner
  - L105 [soft] `skeletal-proof` in `theorem modularBetaFlow_zero` — proof appears to close via minimal tactic one-liner
  - L111 [soft] `skeletal-proof` in `theorem modularBetaFlow_one` — proof appears to close via minimal tactic one-liner
  - L122 [soft] `skeletal-proof` in `theorem modularDeltaFromHamiltonian_eq_exp_neg` — proof appears to close via minimal tactic one-liner
  - L133 [soft] `skeletal-proof` in `theorem modularBetaDeviation_zero` — proof appears to close via minimal tactic one-liner
  - L139 [soft] `skeletal-proof` in `theorem modularBetaDeviation_one` — proof appears to close via minimal tactic one-liner
  - L203 [soft] `skeletal-proof` in `theorem hilbertExpectationAt_zero` — proof appears to close via minimal tactic one-liner
  - L209 [soft] `skeletal-proof` in `theorem kreinExpectationAt_zero` — proof appears to close via minimal tactic one-liner
  - L231 [soft] `skeletal-proof` in `theorem operatorBregman_self` — proof appears to close via minimal tactic one-liner
  - L257 [soft] `skeletal-proof` in `theorem souriauUntracedExponential_zero` — proof appears to close via minimal tactic one-liner
  - L275 [soft] `skeletal-proof` in `theorem souriauUntracedDeviation_zero` — proof appears to close via minimal tactic one-liner

