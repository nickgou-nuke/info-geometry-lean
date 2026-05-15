# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:24.991100+00:00`
Root: `lean/InfoGeometry/Core/SymmetricLieGeneric.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **42**
- Hard: **0**
- Soft: **11**
- Advisory: **31**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Core/SymmetricLieGeneric.lean` | `advisory` | 53 | 0 | 11 | 31 | 42 |

## Findings by file

### `lean/InfoGeometry/Core/SymmetricLieGeneric.lean`
- module: `InfoGeometry.Core.SymmetricLieGeneric`
- status: `advisory`
- debt_score: `53`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L21 [soft] `law-field-locker` in `structure-field SymmetricLieAlgebra.involution` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L24 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L26 [soft] `simp-law-injection` in `simp-declaration involution_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L44 [advisory] `local-hypothesis-injection` in `lemma mem_` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L48 [advisory] `local-hypothesis-injection` in `lemma mem_` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L54 [advisory] `local-hypothesis-injection` in `lemma mem_` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L58 [advisory] `local-hypothesis-injection` in `lemma mem_` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L70 [soft] `simp-law-injection` in `simp-declaration P_plus_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L74 [soft] `simp-law-injection` in `simp-declaration P_minus_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L78 [soft] `skeletal-proof` in `lemma P_plus_fixed` — proof appears to close via minimal tactic one-liner
  - L82 [soft] `skeletal-proof` in `lemma P_minus_neg_fixed` — proof appears to close via minimal tactic one-liner
  - L105 [advisory] `local-hypothesis-injection` in `lemma P_plus_eq_self_of_mem_` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L114 [advisory] `local-hypothesis-injection` in `lemma P_minus_eq_zero_of_mem_` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L122 [advisory] `local-hypothesis-injection` in `lemma P_plus_eq_zero_of_mem_` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L130 [advisory] `local-hypothesis-injection` in `lemma P_minus_eq_self_of_mem_` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L152 [soft] `skeletal-proof` in `theorem cartan_decomposition` — proof appears to close via minimal tactic one-liner
  - L156 [advisory] `local-hypothesis-injection` in `theorem cartan_decomposition` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L203 [advisory] `local-hypothesis-injection` in `theorem disjoint_` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L204 [advisory] `local-hypothesis-injection` in `theorem disjoint_` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L230 [advisory] `local-hypothesis-injection` in `theorem bracket_k_k` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L231 [advisory] `local-hypothesis-injection` in `theorem bracket_k_k` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L237 [advisory] `local-hypothesis-injection` in `theorem bracket_k_p` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L238 [advisory] `local-hypothesis-injection` in `theorem bracket_k_p` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L244 [advisory] `local-hypothesis-injection` in `theorem bracket_p_p` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L245 [advisory] `local-hypothesis-injection` in `theorem bracket_p_p` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L301 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L317 [soft] `skeletal-proof` in `theorem killing_orthogonal` — proof appears to close via minimal tactic one-liner
  - L319 [advisory] `local-hypothesis-injection` in `theorem killing_orthogonal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L320 [advisory] `local-hypothesis-injection` in `theorem killing_orthogonal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L321 [advisory] `local-hypothesis-injection` in `theorem killing_orthogonal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L323 [advisory] `local-hypothesis-injection` in `theorem killing_orthogonal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L325 [advisory] `local-hypothesis-injection` in `theorem killing_orthogonal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L331 [advisory] `local-hypothesis-injection` in `theorem killing_orthogonal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L334 [advisory] `local-hypothesis-injection` in `theorem killing_orthogonal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L337 [advisory] `local-hypothesis-injection` in `theorem killing_orthogonal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L342 [advisory] `local-hypothesis-injection` in `theorem killing_orthogonal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L374 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L399 [soft] `simp-law-injection` in `simp-declaration cartanForm_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L413 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L419 [soft] `law-field-locker` in `structure-field CartanSignature.pos_on_p` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L420 [soft] `law-field-locker` in `structure-field CartanSignature.neg_on_k` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

