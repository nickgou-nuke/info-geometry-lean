# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:35.651685+00:00`
Root: `lean/InfoGeometry/Canonical/OperatorDictionary.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **7**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/OperatorDictionary.lean` | `advisory` | 17 | 0 | 7 | 3 | 10 |

## Findings by file

### `lean/InfoGeometry/Canonical/OperatorDictionary.lean`
- module: `InfoGeometry.Canonical.OperatorDictionary`
- status: `advisory`
- debt_score: `17`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L33 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L35 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L49 [soft] `skeletal-proof` in `theorem u_eq_uPlusComponent_add_uMinusComponent` — proof appears to close via minimal tactic one-liner
  - L65 [soft] `skeletal-proof` in `theorem modular_j_eq_Qplus_add_Qminus` — proof appears to close via minimal tactic one-liner
  - L78 [soft] `skeletal-proof` in `theorem phaseAxisK_eq_modular_j_comp_spectral_epsilon` — proof appears to close via minimal tactic one-liner
  - L85 [soft] `skeletal-proof` in `theorem modular_j_comp_spectral_epsilon_eq_neg_spectral_epsilon_comp_modular_j` — proof appears to close via minimal tactic one-liner
  - L92 [soft] `skeletal-proof` in `theorem phaseAxisK_sq_eq_neg_id` — proof appears to close via minimal tactic one-liner
  - L107 [soft] `skeletal-proof` in `theorem phaseAxisK_kreinInner_comp` — proof appears to close via minimal tactic one-liner
  - L119 [soft] `skeletal-proof` in `theorem phaseAxisObservable_eq_phaseAxisForce` — proof appears to close via minimal tactic one-liner

