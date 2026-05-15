# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:23.297084+00:00`
Root: `lean/InfoGeometry/Canonical/KMSSinkhornSeedState.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **20**
- Hard: **0**
- Soft: **11**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/KMSSinkhornSeedState.lean` | `advisory` | 31 | 0 | 11 | 9 | 20 |

## Findings by file

### `lean/InfoGeometry/Canonical/KMSSinkhornSeedState.lean`
- module: `InfoGeometry.Canonical.KMSSinkhornSeedState`
- status: `advisory`
- debt_score: `31`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L33 [soft] `simp-law-injection` in `simp-declaration expectationSeedFunctional_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L43 [soft] `simp-law-injection` in `simp-declaration omegaSeed_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L48 [soft] `simp-law-injection` in `simp-declaration expectationSeedFunctional_id` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L68 [advisory] `local-hypothesis-injection` in `lemma expectationSeedFunctional_nonzero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L70 [advisory] `local-hypothesis-injection` in `lemma expectationSeedFunctional_nonzero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L71 [advisory] `local-hypothesis-injection` in `lemma expectationSeedFunctional_nonzero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L75 [soft] `skeletal-proof` in `lemma omegaSeed_nonzero` — proof appears to close via minimal tactic one-liner
  - L105 [soft] `simp-law-injection` in `simp-declaration jointKernelOnOmega_beta_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L115 [soft] `skeletal-proof` in `lemma commutatorOrthogonalOnOmega_of_pairwise_commute` — proof appears to close via minimal tactic one-liner
  - L125 [advisory] `local-hypothesis-injection` in `lemma commutatorOrthogonalOnOmega_of_pairwise_commute` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L130 [soft] `skeletal-proof` in `lemma modularShift_eq_self_of_pairwise_commute` — proof appears to close via minimal tactic one-liner
  - L145 [advisory] `local-hypothesis-injection` in `lemma modularShift_eq_self_of_pairwise_commute` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L148 [advisory] `local-hypothesis-injection` in `lemma modularShift_eq_self_of_pairwise_commute` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L183 [soft] `skeletal-proof` in `lemma modularOnOmega_of_jointKernel` — proof appears to close via minimal tactic one-liner
  - L198 [soft] `skeletal-proof` in `lemma cyclicOnOmega_of_commutator_orthogonal` — proof appears to close via minimal tactic one-liner
  - L208 [advisory] `local-hypothesis-injection` in `lemma cyclicOnOmega_of_commutator_orthogonal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L209 [advisory] `local-hypothesis-injection` in `lemma cyclicOnOmega_of_commutator_orthogonal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L213 [soft] `skeletal-proof` in `theorem expectationSeedFunctional_kms_of_structural` — proof appears to close via minimal tactic one-liner
  - L283 [soft] `skeletal-proof` in `theorem omegaSeed_kms_of_beta_zero_of_pairwise_commute` — proof appears to close via minimal tactic one-liner

