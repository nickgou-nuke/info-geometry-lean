# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:19.530059+00:00`
Root: `lean/InfoGeometry/Canonical/IBUpdate.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **51**
- Hard: **0**
- Soft: **11**
- Advisory: **40**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/IBUpdate.lean` | `advisory` | 62 | 0 | 11 | 40 | 51 |

## Findings by file

### `lean/InfoGeometry/Canonical/IBUpdate.lean`
- module: `InfoGeometry.Canonical.IBUpdate`
- status: `advisory`
- debt_score: `62`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L39 [soft] `skeletal-proof` in `theorem ibBlahutArimotoStepFrozen_eq_prior_of_uniformDistortion` — proof appears to close via minimal tactic one-liner
  - L59 [advisory] `local-hypothesis-injection` in `theorem ibBlahutArimotoStepFrozen_eq_prior_of_uniformDistortion` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L64 [advisory] `local-hypothesis-injection` in `theorem ibBlahutArimotoStepFrozen_eq_prior_of_uniformDistortion` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L69 [advisory] `local-hypothesis-injection` in `theorem ibBlahutArimotoStepFrozen_eq_prior_of_uniformDistortion` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L94 [soft] `skeletal-proof` in `lemma ibBlahutArimotoStepFrozen_slice_eq_of_score_scale` — proof appears to close via minimal tactic one-liner
  - L190 [advisory] `local-hypothesis-injection` in `lemma baScore_toReal_le_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L192 [advisory] `local-hypothesis-injection` in `lemma baScore_toReal_le_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L193 [advisory] `local-hypothesis-injection` in `lemma baScore_toReal_le_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L196 [advisory] `local-hypothesis-injection` in `lemma baScore_toReal_le_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L197 [advisory] `local-hypothesis-injection` in `lemma baScore_toReal_le_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L198 [advisory] `local-hypothesis-injection` in `lemma baScore_toReal_le_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L200 [advisory] `local-hypothesis-injection` in `lemma baScore_toReal_le_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L203 [advisory] `local-hypothesis-injection` in `lemma baScore_toReal_le_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L211 [advisory] `local-hypothesis-injection` in `lemma baScore_toReal_le_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L329 [soft] `skeletal-proof` in `lemma ibBlahutArimotoStep_eq_scoreProjectiveGauge` — proof appears to close via minimal tactic one-liner
  - L347 [soft] `skeletal-proof` in `lemma ibBlahutArimotoStep_eq_scoreRayGaugeSection` — proof appears to close via minimal tactic one-liner
  - L359 [soft] `skeletal-proof` in `theorem ibBlahutArimotoStep_eq_of_scoreRay_eq` — proof appears to close via minimal tactic one-liner
  - L460 [advisory] `existential-packaging` in `theorem ibBlahutArimotoStep_dilation_split` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L513 [soft] `skeletal-proof` in `lemma ibBlahutArimotoStep_slice_eq_of_sameScoreRay` — proof appears to close via minimal tactic one-liner
  - L640 [soft] `simp-law-injection` in `simp-declaration baScore_eq_baScoreFrozen_induced` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L650 [soft] `skeletal-proof` in `lemma ibBlahutArimotoStep_eq_frozen_induced` — proof appears to close via minimal tactic one-liner
  - L701 [soft] `skeletal-proof` in `theorem ibBlahutArimotoStep_pointwise_massNndist_le_zero_of_sameScoreRay` — proof appears to close via minimal tactic one-liner
  - L825 [soft] `skeletal-proof` in `theorem ibBlahutArimotoStep_pointwise_massNndist_le_zero_of_scoreRay_eq` — proof appears to close via minimal tactic one-liner
  - L855 [soft] `skeletal-proof` in `theorem ibBlahutArimotoStep_encoderMassNndist_le_zero_of_scoreRay_eq` — proof appears to close via minimal tactic one-liner
  - L1099 [advisory] `local-hypothesis-injection` in `theorem baNormalize_pointwise_massNndist_le_of_massRecipLipschitz` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1113 [advisory] `local-hypothesis-injection` in `theorem baNormalize_pointwise_massNndist_le_of_massRecipLipschitz` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1114 [advisory] `local-hypothesis-injection` in `theorem baNormalize_pointwise_massNndist_le_of_massRecipLipschitz` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1115 [advisory] `local-hypothesis-injection` in `theorem baNormalize_pointwise_massNndist_le_of_massRecipLipschitz` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1116 [advisory] `local-hypothesis-injection` in `theorem baNormalize_pointwise_massNndist_le_of_massRecipLipschitz` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1117 [advisory] `local-hypothesis-injection` in `theorem baNormalize_pointwise_massNndist_le_of_massRecipLipschitz` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1118 [advisory] `local-hypothesis-injection` in `theorem baNormalize_pointwise_massNndist_le_of_massRecipLipschitz` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1119 [advisory] `local-hypothesis-injection` in `theorem baNormalize_pointwise_massNndist_le_of_massRecipLipschitz` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1121 [advisory] `local-hypothesis-injection` in `theorem baNormalize_pointwise_massNndist_le_of_massRecipLipschitz` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1123 [advisory] `local-hypothesis-injection` in `theorem baNormalize_pointwise_massNndist_le_of_massRecipLipschitz` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1125 [advisory] `local-hypothesis-injection` in `theorem baNormalize_pointwise_massNndist_le_of_massRecipLipschitz` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1131 [advisory] `local-hypothesis-injection` in `theorem baNormalize_pointwise_massNndist_le_of_massRecipLipschitz` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1133 [advisory] `local-hypothesis-injection` in `theorem baNormalize_pointwise_massNndist_le_of_massRecipLipschitz` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1135 [advisory] `local-hypothesis-injection` in `theorem baNormalize_pointwise_massNndist_le_of_massRecipLipschitz` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1137 [advisory] `local-hypothesis-injection` in `theorem baNormalize_pointwise_massNndist_le_of_massRecipLipschitz` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1139 [advisory] `local-hypothesis-injection` in `theorem baNormalize_pointwise_massNndist_le_of_massRecipLipschitz` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1142 [advisory] `local-hypothesis-injection` in `theorem baNormalize_pointwise_massNndist_le_of_massRecipLipschitz` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1143 [advisory] `local-hypothesis-injection` in `theorem baNormalize_pointwise_massNndist_le_of_massRecipLipschitz` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1145 [advisory] `local-hypothesis-injection` in `theorem baNormalize_pointwise_massNndist_le_of_massRecipLipschitz` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1148 [advisory] `local-hypothesis-injection` in `theorem baNormalize_pointwise_massNndist_le_of_massRecipLipschitz` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1151 [advisory] `local-hypothesis-injection` in `theorem baNormalize_pointwise_massNndist_le_of_massRecipLipschitz` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1152 [advisory] `local-hypothesis-injection` in `theorem baNormalize_pointwise_massNndist_le_of_massRecipLipschitz` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1154 [advisory] `local-hypothesis-injection` in `theorem baNormalize_pointwise_massNndist_le_of_massRecipLipschitz` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1157 [advisory] `local-hypothesis-injection` in `theorem baNormalize_pointwise_massNndist_le_of_massRecipLipschitz` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1236 [advisory] `local-hypothesis-injection` in `theorem baNormalize_pointwise_massNndist_le_of_massRecipLipschitz_intrinsicUpper` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1460 [advisory] `local-hypothesis-injection` in `theorem ibBlahutArimotoStep_encoderNndist_le_of_pointwise` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

