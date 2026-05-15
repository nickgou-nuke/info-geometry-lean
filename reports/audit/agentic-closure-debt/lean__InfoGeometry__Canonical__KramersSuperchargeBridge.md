# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:24.242642+00:00`
Root: `lean/InfoGeometry/Canonical/KramersSuperchargeBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **17**
- Hard: **0**
- Soft: **8**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/KramersSuperchargeBridge.lean` | `advisory` | 25 | 0 | 8 | 9 | 17 |

## Findings by file

### `lean/InfoGeometry/Canonical/KramersSuperchargeBridge.lean`
- module: `InfoGeometry.Canonical.KramersSuperchargeBridge`
- status: `advisory`
- debt_score: `25`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L26 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L28 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L67 [soft] `skeletal-proof` in `theorem qD_is_odd` — proof appears to close via minimal tactic one-liner
  - L74 [soft] `skeletal-proof` in `theorem hD_is_even` — proof appears to close via minimal tactic one-liner
  - L81 [soft] `skeletal-proof` in `theorem hD_eq_hK_add_zD` — proof appears to close via minimal tactic one-liner
  - L108 [advisory] `bridge-shaped-declaration` in `theorem kramersPair_phasePartner_bridge` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L125 [soft] `skeletal-proof` in `theorem kramers_conjugated_qD_is_odd_of_commute_GammaS` — proof appears to close via minimal tactic one-liner
  - L130 [advisory] `local-hypothesis-injection` in `theorem kramers_conjugated_qD_is_odd_of_commute_GammaS` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L153 [soft] `skeletal-proof` in `theorem majorana_fixed_closed_of_commute` — proof appears to close via minimal tactic one-liner
  - L191 [soft] `skeletal-proof` in `theorem commute_C_QD_of_commute_C_chi` — proof appears to close via minimal tactic one-liner
  - L198 [advisory] `local-hypothesis-injection` in `theorem commute_C_QD_of_commute_C_chi` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L199 [advisory] `local-hypothesis-injection` in `theorem commute_C_QD_of_commute_C_chi` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L209 [soft] `skeletal-proof` in `theorem commute_C_HD_of_commute_C_QD` — proof appears to close via minimal tactic one-liner
  - L215 [advisory] `local-hypothesis-injection` in `theorem commute_C_HD_of_commute_C_QD` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L273 [advisory] `local-hypothesis-injection` in `theorem commute_C_ZD_of_commute_chi_and_Q0` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L302 [soft] `skeletal-proof` in `theorem commute_C_HK_of_commute_chi_and_Q0` — proof appears to close via minimal tactic one-liner

