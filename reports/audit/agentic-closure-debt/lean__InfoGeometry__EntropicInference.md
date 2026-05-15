# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:26.634534+00:00`
Root: `lean/InfoGeometry/EntropicInference.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **43**
- Hard: **0**
- Soft: **7**
- Advisory: **36**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/EntropicInference.lean` | `advisory` | 50 | 0 | 7 | 36 | 43 |

## Findings by file

### `lean/InfoGeometry/EntropicInference.lean`
- module: `InfoGeometry.EntropicInference`
- status: `advisory`
- debt_score: `50`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L58 [advisory] `local-hypothesis-injection` in `def cond_theta_given_x` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L69 [soft] `skeletal-proof` in `lemma cond_theta_given_x_apply` — proof appears to close via minimal tactic one-liner
  - L127 [soft] `skeletal-proof` in `lemma marginal_x_jeffrey_joint` — proof appears to close via minimal tactic one-liner
  - L162 [advisory] `existential-packaging` in `lemma marginal_x_toReal_pos_of_joint_toReal_pos` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L162 [soft] `classical-witness-smuggling` in `lemma marginal_x_toReal_pos_of_joint_toReal_pos` — declaration uses Classical/choice/Nonempty witness extraction; require constructive payload readback or explicit nonconstructive boundary
  - L162 [soft] `skeletal-proof` in `lemma marginal_x_toReal_pos_of_joint_toReal_pos` — proof appears to close via minimal tactic one-liner
  - L172 [advisory] `local-hypothesis-injection` in `lemma marginal_x_toReal_pos_of_joint_toReal_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L173 [advisory] `local-hypothesis-injection` in `lemma marginal_x_toReal_pos_of_joint_toReal_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L175 [advisory] `local-hypothesis-injection` in `lemma marginal_x_toReal_pos_of_joint_toReal_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L186 [advisory] `local-hypothesis-injection` in `lemma marginal_x_toReal_pos_of_joint_toReal_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L191 [advisory] `existential-packaging` in `lemma marginal_x_full_support_of_joint_toReal_pos` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L200 [advisory] `local-hypothesis-injection` in `lemma marginal_x_full_support_of_joint_toReal_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L209 [advisory] `existential-packaging` in `lemma cond_theta_given_x_toReal_ratio` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L224 [advisory] `existential-packaging` in `lemma joint_toReal_factor_marginal_conditional` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L235 [advisory] `local-hypothesis-injection` in `lemma joint_toReal_factor_marginal_conditional` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L243 [advisory] `existential-packaging` in `lemma pointwise_log_split` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L292 [advisory] `existential-packaging` in `theorem kl_chain_rule_toReal_strict` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L317 [advisory] `local-hypothesis-injection` in `theorem kl_chain_rule_toReal_strict` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L321 [advisory] `local-hypothesis-injection` in `theorem kl_chain_rule_toReal_strict` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L323 [advisory] `local-hypothesis-injection` in `theorem kl_chain_rule_toReal_strict` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L327 [advisory] `local-hypothesis-injection` in `theorem kl_chain_rule_toReal_strict` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L386 [advisory] `local-hypothesis-injection` in `theorem kl_chain_rule_toReal_strict` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L409 [soft] `skeletal-proof` in `lemma cond_theta_given_x_assemble` — proof appears to close via minimal tactic one-liner
  - L421 [advisory] `local-hypothesis-injection` in `lemma cond_theta_given_x_assemble` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L431 [soft] `skeletal-proof` in `lemma cond_theta_given_x_jeffrey_joint` — proof appears to close via minimal tactic one-liner
  - L445 [advisory] `existential-packaging` in `theorem kl_pythagorean_jeffrey_toReal_strict` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L469 [advisory] `local-hypothesis-injection` in `theorem kl_pythagorean_jeffrey_toReal_strict` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L473 [advisory] `local-hypothesis-injection` in `theorem kl_pythagorean_jeffrey_toReal_strict` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L481 [advisory] `local-hypothesis-injection` in `theorem kl_pythagorean_jeffrey_toReal_strict` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L487 [advisory] `local-hypothesis-injection` in `theorem kl_pythagorean_jeffrey_toReal_strict` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L490 [advisory] `local-hypothesis-injection` in `theorem kl_pythagorean_jeffrey_toReal_strict` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L492 [advisory] `local-hypothesis-injection` in `theorem kl_pythagorean_jeffrey_toReal_strict` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L583 [advisory] `local-hypothesis-injection` in `lemma kl_div_ne_top_of_right_toReal_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L589 [advisory] `existential-packaging` in `theorem kl_pythagorean_jeffrey_strict` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L589 [soft] `skeletal-proof` in `theorem kl_pythagorean_jeffrey_strict` — proof appears to close via minimal tactic one-liner
  - L621 [advisory] `local-hypothesis-injection` in `theorem kl_pythagorean_jeffrey_strict` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L624 [advisory] `local-hypothesis-injection` in `theorem kl_pythagorean_jeffrey_strict` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L626 [advisory] `local-hypothesis-injection` in `theorem kl_pythagorean_jeffrey_strict` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L630 [advisory] `local-hypothesis-injection` in `theorem kl_pythagorean_jeffrey_strict` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L636 [advisory] `local-hypothesis-injection` in `theorem kl_pythagorean_jeffrey_strict` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L640 [advisory] `local-hypothesis-injection` in `theorem kl_pythagorean_jeffrey_strict` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L644 [advisory] `local-hypothesis-injection` in `theorem kl_pythagorean_jeffrey_strict` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

