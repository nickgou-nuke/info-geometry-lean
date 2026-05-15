# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:17.260158+00:00`
Root: `lean/InfoGeometry/Canonical/IBFinitePythagorean.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **28**
- Hard: **0**
- Soft: **2**
- Advisory: **26**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/IBFinitePythagorean.lean` | `advisory` | 30 | 0 | 2 | 26 | 28 |

## Findings by file

### `lean/InfoGeometry/Canonical/IBFinitePythagorean.lean`
- module: `InfoGeometry.Canonical.IBFinitePythagorean`
- status: `advisory`
- debt_score: `30`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L199 [advisory] `local-hypothesis-injection` in `lemma pmf_absolutelyContinuous_of_supportFaithful` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L203 [advisory] `local-hypothesis-injection` in `lemma pmf_absolutelyContinuous_of_supportFaithful` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L220 [soft] `skeletal-proof` in `lemma toReal_fin_klDiv_eq_sum_log_ratio_of_supportFaithful` — proof appears to close via minimal tactic one-liner
  - L231 [advisory] `local-hypothesis-injection` in `lemma toReal_fin_klDiv_eq_sum_log_ratio_of_supportFaithful` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L305 [advisory] `local-hypothesis-injection` in `lemma integral_exp_neg_distortion_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L308 [advisory] `local-hypothesis-injection` in `lemma integral_exp_neg_distortion_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L382 [advisory] `local-hypothesis-injection` in `lemma probMeasureToPMF_IBNextEncoder_toReal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L398 [advisory] `local-hypothesis-injection` in `lemma IBNextEncoder_positive_of_ref_positive` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L413 [advisory] `local-hypothesis-injection` in `lemma ref_positive_of_IBNextEncoder_positive` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L442 [advisory] `local-hypothesis-injection` in `lemma IBNextMarginal_positive_of_ref_positive` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L444 [advisory] `local-hypothesis-injection` in `lemma IBNextMarginal_positive_of_ref_positive` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L449 [advisory] `local-hypothesis-injection` in `lemma IBNextMarginal_positive_of_ref_positive` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L451 [advisory] `local-hypothesis-injection` in `lemma IBNextMarginal_positive_of_ref_positive` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L452 [advisory] `local-hypothesis-injection` in `lemma IBNextMarginal_positive_of_ref_positive` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L453 [advisory] `local-hypothesis-injection` in `lemma IBNextMarginal_positive_of_ref_positive` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L496 [advisory] `existential-packaging` in `lemma pmf_bind_supportFaithful_ref` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L496 [soft] `skeletal-proof` in `lemma pmf_bind_supportFaithful_ref` — proof appears to close via minimal tactic one-liner
  - L511 [advisory] `local-hypothesis-injection` in `lemma pmf_bind_supportFaithful_ref` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L513 [advisory] `local-hypothesis-injection` in `lemma pmf_bind_supportFaithful_ref` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L515 [advisory] `local-hypothesis-injection` in `lemma pmf_bind_supportFaithful_ref` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L517 [advisory] `local-hypothesis-injection` in `lemma pmf_bind_supportFaithful_ref` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L518 [advisory] `local-hypothesis-injection` in `lemma pmf_bind_supportFaithful_ref` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L563 [advisory] `local-hypothesis-injection` in `lemma IBNextMarginal_positive_of_encoder_positive` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L564 [advisory] `local-hypothesis-injection` in `lemma IBNextMarginal_positive_of_encoder_positive` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L565 [advisory] `local-hypothesis-injection` in `lemma IBNextMarginal_positive_of_encoder_positive` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L583 [advisory] `local-hypothesis-injection` in `lemma log_div_split` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L797 [advisory] `local-hypothesis-injection` in `theorem ibMarginalPythagoreanWitness_finite_supportFaithful` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

