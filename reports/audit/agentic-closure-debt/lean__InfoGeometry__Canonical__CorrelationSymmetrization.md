# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:57.315711+00:00`
Root: `lean/InfoGeometry/Canonical/CorrelationSymmetrization.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **3**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/CorrelationSymmetrization.lean` | `advisory` | 8 | 0 | 3 | 2 | 5 |

## Findings by file

### `lean/InfoGeometry/Canonical/CorrelationSymmetrization.lean`
- module: `InfoGeometry.Canonical.CorrelationSymmetrization`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L33 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L138 [soft] `skeletal-proof` in `theorem comparisonStateGeneratorPhase_eq_phaseShiftedTwoStateChannelCorrelation_self` — proof appears to close via minimal tactic one-liner
  - L152 [soft] `skeletal-proof` in `theorem toRelationalInformationDatum_comparisonGeneratorMetric_eq_symmetricTwoStateChannelCorrelation_self` — proof appears to close via minimal tactic one-liner
  - L175 [soft] `skeletal-proof` in `theorem toRelationalInformationDatum_comparisonGeneratorPhase_eq_phaseShiftedTwoStateChannelCorrelation_self` — proof appears to close via minimal tactic one-liner

