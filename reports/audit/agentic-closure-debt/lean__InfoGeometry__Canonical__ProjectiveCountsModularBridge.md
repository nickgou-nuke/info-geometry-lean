# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:44.840905+00:00`
Root: `lean/InfoGeometry/Canonical/ProjectiveCountsModularBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **11**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ProjectiveCountsModularBridge.lean` | `advisory` | 26 | 0 | 11 | 4 | 15 |

## Findings by file

### `lean/InfoGeometry/Canonical/ProjectiveCountsModularBridge.lean`
- module: `InfoGeometry.Canonical.ProjectiveCountsModularBridge`
- status: `advisory`
- debt_score: `26`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L113 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L124 [soft] `skeletal-proof` in `theorem relativeCountRatio_common_smul` — proof appears to close via minimal tactic one-liner
  - L142 [soft] `skeletal-proof` in `theorem countModularScalar_common_smul` — proof appears to close via minimal tactic one-liner
  - L165 [soft] `simp-law-injection` in `simp-declaration scalarOperatorLift_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L167 [soft] `skeletal-proof` in `theorem scalarOperatorLift_apply` — proof appears to close via minimal tactic one-liner
  - L172 [soft] `simp-law-injection` in `simp-declaration scalarOperatorLift_common_smul_readback` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L174 [advisory] `bridge-shaped-declaration` in `theorem scalarOperatorLift_common_smul_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L188 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L204 [soft] `simp-law-injection` in `simp-declaration countScalarOperatorLift_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L206 [soft] `skeletal-proof` in `theorem countScalarOperatorLift_apply` — proof appears to close via minimal tactic one-liner
  - L212 [soft] `simp-law-injection` in `simp-declaration countKreinOperatorLift_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L214 [soft] `skeletal-proof` in `theorem countKreinOperatorLift_apply` — proof appears to close via minimal tactic one-liner
  - L224 [soft] `skeletal-proof` in `theorem countScalarOperatorLift_common_smul` — proof appears to close via minimal tactic one-liner
  - L236 [soft] `skeletal-proof` in `theorem countKreinOperatorLift_common_smul` — proof appears to close via minimal tactic one-liner

