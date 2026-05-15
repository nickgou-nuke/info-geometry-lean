# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:12.491416+00:00`
Root: `lean/InfoGeometry/Canonical/WeylKKTAnomalyIdentity.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **14**
- Hard: **0**
- Soft: **4**
- Advisory: **10**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/WeylKKTAnomalyIdentity.lean` | `advisory` | 18 | 0 | 4 | 10 | 14 |

## Findings by file

### `lean/InfoGeometry/Canonical/WeylKKTAnomalyIdentity.lean`
- module: `InfoGeometry.Canonical.WeylKKTAnomalyIdentity`
- status: `advisory`
- debt_score: `18`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L34 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L48 [soft] `skeletal-proof` in `theorem clifford_decomposition_kkt_form` — proof appears to close via minimal tactic one-liner
  - L52 [advisory] `local-hypothesis-injection` in `theorem clifford_decomposition_kkt_form` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L77 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L79 [soft] `simp-law-injection` in `simp-declaration chiralScale_eq_epsilon` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L87 [soft] `simp-law-injection` in `simp-declaration epsilon_eq_projectorObstruction_nnnorm` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L136 [soft] `skeletal-proof` in `theorem projectorObstruction_eq_zero_and_dilationCommutator_eq_zero_of_structuredProjectorHypotheses_of_chiralScale_eq_zero` — proof appears to close via minimal tactic one-liner
  - L144 [advisory] `local-hypothesis-injection` in `theorem projectorObstruction_eq_zero_and_dilationCommutator_eq_zero_of_structuredProjectorHypotheses_of_chiralScale_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L146 [advisory] `local-hypothesis-injection` in `theorem projectorObstruction_eq_zero_and_dilationCommutator_eq_zero_of_structuredProjectorHypotheses_of_chiralScale_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L149 [advisory] `local-hypothesis-injection` in `theorem projectorObstruction_eq_zero_and_dilationCommutator_eq_zero_of_structuredProjectorHypotheses_of_chiralScale_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L170 [advisory] `local-hypothesis-injection` in `theorem semanticCollapsePacket_of_structuredProjectorHypotheses_of_chiralScale_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L186 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

