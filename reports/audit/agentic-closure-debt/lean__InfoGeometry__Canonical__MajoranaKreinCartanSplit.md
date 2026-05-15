# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:27.069711+00:00`
Root: `lean/InfoGeometry/Canonical/MajoranaKreinCartanSplit.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **21**
- Hard: **0**
- Soft: **18**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/MajoranaKreinCartanSplit.lean` | `advisory` | 39 | 0 | 18 | 3 | 21 |

## Findings by file

### `lean/InfoGeometry/Canonical/MajoranaKreinCartanSplit.lean`
- module: `InfoGeometry.Canonical.MajoranaKreinCartanSplit`
- status: `advisory`
- debt_score: `39`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L37 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L43 [soft] `simp-law-injection` in `simp-declaration projectiveDynamics_J_eq_projectiveMap_tomitaAtomSeed_J` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L47 [soft] `skeletal-proof` in `theorem projectiveDynamics_J_eq_projectiveMap_tomitaAtomSeed_J` — proof appears to close via minimal tactic one-liner
  - L51 [soft] `simp-law-injection` in `simp-declaration projectiveDynamics_epsilon_eq_projectiveMap_tomitaAtomSeed_eps` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L53 [soft] `skeletal-proof` in `theorem projectiveDynamics_epsilon_eq_projectiveMap_tomitaAtomSeed_eps` — proof appears to close via minimal tactic one-liner
  - L57 [soft] `simp-law-injection` in `simp-declaration projectiveDynamics_I_eq_projectiveMap_tomitaAtomSeed_phaseAxis` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L59 [soft] `skeletal-proof` in `theorem projectiveDynamics_I_eq_projectiveMap_tomitaAtomSeed_phaseAxis` — proof appears to close via minimal tactic one-liner
  - L84 [soft] `skeletal-proof` in `theorem comparisonTransportGenerator_eq_gauge_add_source` — proof appears to close via minimal tactic one-liner
  - L94 [soft] `simp-law-injection` in `simp-declaration comparisonGaugeGenerator_eq_phaseLinearPart_comparisonTransportGenerator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L96 [soft] `skeletal-proof` in `theorem comparisonGaugeGenerator_eq_phaseLinearPart_comparisonTransportGenerator` — proof appears to close via minimal tactic one-liner
  - L102 [soft] `simp-law-injection` in `simp-declaration comparisonSourceGenerator_eq_phaseAntilinearPart_comparisonTransportGenerator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L104 [soft] `skeletal-proof` in `theorem comparisonSourceGenerator_eq_phaseAntilinearPart_comparisonTransportGenerator` — proof appears to close via minimal tactic one-liner
  - L112 [soft] `skeletal-proof` in `theorem comparisonGaugeGenerator_isPhaseLinear` — proof appears to close via minimal tactic one-liner
  - L121 [soft] `skeletal-proof` in `theorem comparisonSourceGenerator_isPhaseAntilinear` — proof appears to close via minimal tactic one-liner
  - L128 [soft] `simp-law-injection` in `simp-declaration comparisonGaugeDynamics_eq_transportCommutator_phaseLinearPart` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L130 [soft] `skeletal-proof` in `theorem comparisonGaugeDynamics_eq_transportCommutator_phaseLinearPart` — proof appears to close via minimal tactic one-liner
  - L138 [soft] `simp-law-injection` in `simp-declaration comparisonSourceDynamics_eq_transportCommutator_phaseAntilinearPart` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L140 [soft] `skeletal-proof` in `theorem comparisonSourceDynamics_eq_transportCommutator_phaseAntilinearPart` — proof appears to close via minimal tactic one-liner
  - L220 [soft] `skeletal-proof` in `theorem isPotentialKillingOperator_iff_comparisonReadoutStationary` — proof appears to close via minimal tactic one-liner

