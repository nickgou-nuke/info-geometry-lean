# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:41.520735+00:00`
Root: `lean/InfoGeometry/Canonical/PhaseAxisCartanSymmetricLie.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **6**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/PhaseAxisCartanSymmetricLie.lean` | `advisory` | 21 | 0 | 6 | 9 | 15 |

## Findings by file

### `lean/InfoGeometry/Canonical/PhaseAxisCartanSymmetricLie.lean`
- module: `InfoGeometry.Canonical.PhaseAxisCartanSymmetricLie`
- status: `advisory`
- debt_score: `21`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L34 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L35 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L44 [soft] `skeletal-proof` in `lemma phaseConjugate_phaseConjugate` — proof appears to close via minimal tactic one-liner
  - L47 [advisory] `local-hypothesis-injection` in `lemma phaseConjugate_phaseConjugate` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L80 [soft] `skeletal-proof` in `lemma phaseConjugate_comp_phaseConjugate` — proof appears to close via minimal tactic one-liner
  - L85 [advisory] `local-hypothesis-injection` in `lemma phaseConjugate_comp_phaseConjugate` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L100 [soft] `skeletal-proof` in `lemma phaseAxisCartanMap_lie` — proof appears to close via minimal tactic one-liner
  - L105 [advisory] `local-hypothesis-injection` in `lemma phaseAxisCartanMap_lie` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L106 [advisory] `local-hypothesis-injection` in `lemma phaseAxisCartanMap_lie` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L175 [soft] `skeletal-proof` in `lemma clockAxis_mem_phaseAxis_even` — proof appears to close via minimal tactic one-liner
  - L178 [advisory] `local-hypothesis-injection` in `lemma clockAxis_mem_phaseAxis_even` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L234 [soft] `skeletal-proof` in `theorem scaleClock_commutator_mem_phaseAxis_odd` — proof appears to close via minimal tactic one-liner
  - L247 [soft] `skeletal-proof` in `theorem gaugeClock_commutator_mem_phaseAxis_even` — proof appears to close via minimal tactic one-liner

