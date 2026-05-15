# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:18.679412+00:00`
Root: `lean/InfoGeometry/Canonical/IBProjective.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **22**
- Hard: **0**
- Soft: **14**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/IBProjective.lean` | `advisory` | 36 | 0 | 14 | 8 | 22 |

## Findings by file

### `lean/InfoGeometry/Canonical/IBProjective.lean`
- module: `InfoGeometry.Canonical.IBProjective`
- status: `advisory`
- debt_score: `36`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L17 [soft] `skeletal-proof` in `lemma pmf_normalize_eq_of_scale` — proof appears to close via minimal tactic one-liner
  - L64 [advisory] `existential-packaging` in `def SameScoreRay` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L76 [soft] `skeletal-proof` in `lemma SameScoreRay.symm` — proof appears to close via minimal tactic one-liner
  - L83 [advisory] `local-hypothesis-injection` in `lemma SameScoreRay.symm` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L182 [soft] `law-field-locker` in `structure-field ScoreSlice.f` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L183 [soft] `law-field-locker` in `structure-field ScoreSlice.nonzero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L184 [soft] `law-field-locker` in `structure-field ScoreSlice.finite` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L209 [advisory] `existential-packaging` in `def gaugeSection` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L221 [soft] `simp-law-injection` in `simp-declaration gaugeSection_mk` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L234 [soft] `simp-law-injection` in `simp-declaration normalize_toProjectiveState` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L251 [soft] `simp-law-injection` in `simp-declaration projectiveState_mk` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L254 [soft] `simp-law-injection` in `simp-declaration normalize_projectiveState` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L271 [soft] `law-field-locker` in `structure-field FullSupportScoreSlice.pointwise_nonzero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L272 [soft] `law-field-locker` in `structure-field FullSupportScoreSlice.pointwise_finite` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L296 [soft] `simp-law-injection` in `simp-declaration toPositiveMeasure_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L328 [soft] `simp-law-injection` in `simp-declaration positiveRay_mk` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L333 [soft] `skeletal-proof` in `lemma score_radial_projective_factorization` — proof appears to close via minimal tactic one-liner
  - L347 [advisory] `local-hypothesis-injection` in `lemma score_radial_projective_factorization` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L369 [advisory] `local-hypothesis-injection` in `lemma pmf_normalize_eq_self` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L371 [advisory] `local-hypothesis-injection` in `lemma pmf_normalize_eq_self` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L377 [advisory] `local-hypothesis-injection` in `lemma pmf_normalize_eq_self` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

