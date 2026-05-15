# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:24.315132+00:00`
Root: `lean/InfoGeometry/Core/Involution.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **35**
- Hard: **0**
- Soft: **22**
- Advisory: **13**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Core/Involution.lean` | `advisory` | 57 | 0 | 22 | 13 | 35 |

## Findings by file

### `lean/InfoGeometry/Core/Involution.lean`
- module: `InfoGeometry.Core.Involution`
- status: `advisory`
- debt_score: `57`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L16 [soft] `law-field-locker` in `structure-field InvolutiveAutomorphism.toFun` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L35 [advisory] `local-hypothesis-injection` in `abbrev Involution` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L37 [advisory] `local-hypothesis-injection` in `abbrev Involution` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L45 [soft] `law-field-locker` in `class-field PreservesLinear.map_add` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L46 [soft] `law-field-locker` in `class-field PreservesLinear.map_smul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `class-field PreservesMul.map_mul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L56 [soft] `law-field-locker` in `class-field PreservesMul.map_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `law-field-locker` in `class-field PreservesLieBracket.map_lie` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L97 [soft] `simp-law-injection` in `simp-declaration map_neg` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L99 [soft] `skeletal-proof` in `lemma map_neg` — proof appears to close via minimal tactic one-liner
  - L102 [soft] `simp-law-injection` in `simp-declaration map_sub` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L104 [soft] `skeletal-proof` in `lemma map_sub` — proof appears to close via minimal tactic one-liner
  - L129 [soft] `skeletal-proof` in `lemma map_one` — proof appears to close via minimal tactic one-liner
  - L133 [soft] `simp-law-injection` in `simp-declaration map_inv` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L142 [soft] `simp-law-injection` in `simp-declaration map_div` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L174 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L178 [soft] `simp-law-injection` in `simp-declaration involutive` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L208 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L212 [soft] `simp-law-injection` in `simp-declaration involutive` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L224 [soft] `simp-law-injection` in `simp-declaration map_inv` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L228 [soft] `simp-law-injection` in `simp-declaration map_div` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L240 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L249 [soft] `skeletal-proof` in `lemma decomposition` — proof appears to close via minimal tactic one-liner
  - L252 [advisory] `local-hypothesis-injection` in `lemma decomposition` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L270 [soft] `skeletal-proof` in `lemma plus_fixed` — proof appears to close via minimal tactic one-liner
  - L280 [soft] `skeletal-proof` in `lemma minus_neg_fixed` — proof appears to close via minimal tactic one-liner
  - L314 [soft] `skeletal-proof` in `lemma plus_idempotent` — proof appears to close via minimal tactic one-liner
  - L318 [advisory] `local-hypothesis-injection` in `lemma plus_idempotent` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L327 [soft] `skeletal-proof` in `lemma minus_idempotent` — proof appears to close via minimal tactic one-liner
  - L331 [advisory] `local-hypothesis-injection` in `lemma minus_idempotent` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L360 [advisory] `local-hypothesis-injection` in `lemma fixed_iff_minus_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L361 [advisory] `local-hypothesis-injection` in `lemma fixed_iff_minus_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L376 [advisory] `local-hypothesis-injection` in `lemma neg_fixed_iff_plus_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L377 [advisory] `local-hypothesis-injection` in `lemma neg_fixed_iff_plus_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

