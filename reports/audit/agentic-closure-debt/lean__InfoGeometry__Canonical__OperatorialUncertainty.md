# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:39.692598+00:00`
Root: `lean/InfoGeometry/Canonical/OperatorialUncertainty.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **23**
- Hard: **0**
- Soft: **12**
- Advisory: **11**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/OperatorialUncertainty.lean` | `advisory` | 35 | 0 | 12 | 11 | 23 |

## Findings by file

### `lean/InfoGeometry/Canonical/OperatorialUncertainty.lean`
- module: `InfoGeometry.Canonical.OperatorialUncertainty`
- status: `advisory`
- debt_score: `35`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L37 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L39 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L46 [soft] `skeletal-proof` in `theorem inner_sq_add_modularComplexI_inner_sq_le` — proof appears to close via minimal tactic one-liner
  - L54 [advisory] `local-hypothesis-injection` in `theorem inner_sq_add_modularComplexI_inner_sq_le` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L57 [advisory] `local-hypothesis-injection` in `theorem inner_sq_add_modularComplexI_inner_sq_le` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L65 [advisory] `local-hypothesis-injection` in `theorem inner_sq_add_modularComplexI_inner_sq_le` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L66 [advisory] `local-hypothesis-injection` in `theorem inner_sq_add_modularComplexI_inner_sq_le` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L75 [advisory] `local-hypothesis-injection` in `theorem inner_sq_add_modularComplexI_inner_sq_le` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L77 [advisory] `local-hypothesis-injection` in `theorem inner_sq_add_modularComplexI_inner_sq_le` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L79 [advisory] `local-hypothesis-injection` in `theorem inner_sq_add_modularComplexI_inner_sq_le` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L82 [advisory] `local-hypothesis-injection` in `theorem inner_sq_add_modularComplexI_inner_sq_le` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L123 [soft] `skeletal-proof` in `theorem inner_sq_add_complex_i_inner_sq_le` — proof appears to close via minimal tactic one-liner
  - L130 [soft] `simp-law-injection` in `simp-declaration comparisonStateGeneratorMetric_channelPhaseAxis_left_eq_phase` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L133 [soft] `skeletal-proof` in `theorem comparisonStateGeneratorMetric_channelPhaseAxis_left_eq_phase` — proof appears to close via minimal tactic one-liner
  - L147 [soft] `skeletal-proof` in `theorem comparisonStateGeneratorMetric_channelPhaseAxis_self_eq_self_of_IsPhaseLinear` — proof appears to close via minimal tactic one-liner
  - L216 [soft] `skeletal-proof` in `theorem comparisonStateGeneratorMetric_sq_add_phase_sq_le_of_IsPhaseLinear` — proof appears to close via minimal tactic one-liner
  - L261 [soft] `skeletal-proof` in `theorem inv_comparisonStateGeneratorMetric_self_le_of_unit_phase_response_of_IsPhaseLinear` — proof appears to close via minimal tactic one-liner
  - L292 [soft] `skeletal-proof` in `theorem phaseShiftedTwoStateChannelCorrelation_self_sq_le_of_IsPhaseLinear` — proof appears to close via minimal tactic one-liner
  - L330 [soft] `skeletal-proof` in `theorem symmetricTwoStateChannelCorrelation_sq_add_phaseShifted_sq_le_of_IsPhaseLinear` — proof appears to close via minimal tactic one-liner
  - L376 [soft] `skeletal-proof` in `theorem toRelationalInformationDatum_comparisonGeneratorPhase_sq_le_of_IsPhaseLinear` — proof appears to close via minimal tactic one-liner
  - L398 [soft] `skeletal-proof` in `theorem toRelationalInformationDatum_comparisonGeneratorMetric_sq_add_phase_sq_le_of_IsPhaseLinear` — proof appears to close via minimal tactic one-liner
  - L424 [soft] `skeletal-proof` in `theorem toRelationalInformationDatum_inv_comparisonGeneratorMetric_self_le_of_unit_phase_response_of_IsPhaseLinear` — proof appears to close via minimal tactic one-liner

