# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:29.646200+00:00`
Root: `lean/InfoGeometry/ExponentialFamily/Gaussian.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **5**
- Advisory: **13**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/ExponentialFamily/Gaussian.lean` | `advisory` | 23 | 0 | 5 | 13 | 18 |

## Findings by file

### `lean/InfoGeometry/ExponentialFamily/Gaussian.lean`
- module: `InfoGeometry.ExponentialFamily.Gaussian`
- status: `advisory`
- debt_score: `23`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L21 [soft] `law-field-locker` in `structure-field GaussianFamily.sigma` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L22 [soft] `law-field-locker` in `structure-field GaussianFamily.sigma_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L26 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L32 [soft] `skeletal-proof` in `lemma hasFDerivAt_logPartition` — proof appears to close via minimal tactic one-liner
  - L37 [advisory] `local-hypothesis-injection` in `lemma hasFDerivAt_logPartition` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L39 [advisory] `local-hypothesis-injection` in `lemma hasFDerivAt_logPartition` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L46 [advisory] `local-hypothesis-injection` in `lemma hasFDerivAt_logPartition` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L48 [advisory] `local-hypothesis-injection` in `lemma hasFDerivAt_logPartition` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L54 [soft] `skeletal-proof` in `lemma divergence_form_nonneg` — proof appears to close via minimal tactic one-liner
  - L63 [advisory] `local-hypothesis-injection` in `lemma divergence_form_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L68 [advisory] `local-hypothesis-injection` in `lemma divergence_form_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L72 [advisory] `local-hypothesis-injection` in `lemma divergence_form_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L92 [soft] `skeletal-proof` in `theorem divergence_eq_mahalanobis` — proof appears to close via minimal tactic one-liner
  - L97 [advisory] `local-hypothesis-injection` in `theorem divergence_eq_mahalanobis` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L102 [advisory] `local-hypothesis-injection` in `theorem divergence_eq_mahalanobis` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L106 [advisory] `local-hypothesis-injection` in `theorem divergence_eq_mahalanobis` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L110 [advisory] `existential-packaging` in `def softmaxGaussianAttention` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

