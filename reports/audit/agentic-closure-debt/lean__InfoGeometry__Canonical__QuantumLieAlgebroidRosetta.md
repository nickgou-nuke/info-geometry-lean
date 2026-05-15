# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:46.751516+00:00`
Root: `lean/InfoGeometry/Canonical/QuantumLieAlgebroidRosetta.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **14**
- Hard: **0**
- Soft: **11**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/QuantumLieAlgebroidRosetta.lean` | `advisory` | 25 | 0 | 11 | 3 | 14 |

## Findings by file

### `lean/InfoGeometry/Canonical/QuantumLieAlgebroidRosetta.lean`
- module: `InfoGeometry.Canonical.QuantumLieAlgebroidRosetta`
- status: `advisory`
- debt_score: `25`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L29 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L31 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L37 [soft] `simp-law-injection` in `simp-declaration internalPhaseAxis_eq_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L41 [soft] `simp-law-injection` in `simp-declaration paper_complexUnit_eq_internalPhaseAxis` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L51 [soft] `simp-law-injection` in `simp-declaration paper_channelPhaseAxis_apply_eq_comp_internalPhaseAxis` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L60 [soft] `simp-law-injection` in `simp-declaration paper_generatorPhase_eq_metric_comp_internalPhaseAxis` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L71 [soft] `simp-law-injection` in `simp-declaration paper_anchor_eq_comparisonInducedDynamics` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L84 [soft] `simp-law-injection` in `simp-declaration paper_anchor_split_eq_gauge_add_source` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L96 [soft] `simp-law-injection` in `simp-declaration paper_schrodingerCurrent_eq_probe_anchor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L109 [soft] `simp-law-injection` in `simp-declaration paper_metricPhase_pair_eq_metricBerry_of_anchor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L127 [soft] `simp-law-injection` in `simp-declaration paper_phaseReadout_eq_metric_comp_internalPhaseAxis` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L142 [soft] `simp-law-injection` in `simp-declaration paper_phaseReadout_eq_metric_comp_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L152 [soft] `simp-law-injection` in `simp-declaration paper_inducedDatum_anchor_eq_stateInducedDynamics` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

