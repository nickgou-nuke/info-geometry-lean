# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:28.454027+00:00`
Root: `lean/InfoGeometry/PositiveMeasure.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **31**
- Hard: **0**
- Soft: **12**
- Advisory: **19**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/PositiveMeasure.lean` | `advisory` | 43 | 0 | 12 | 19 | 31 |

## Findings by file

### `lean/InfoGeometry/PositiveMeasure.lean`
- module: `InfoGeometry.PositiveMeasure`
- status: `advisory`
- debt_score: `43`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [soft] `law-field-locker` in `structure-field PositiveMeasure.mass` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L36 [soft] `law-field-locker` in `structure-field PositiveMeasure.pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L44 [soft] `law-field-locker` in `structure-field PositiveMeasure.instance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `simp-law-injection` in `simp-declaration pos_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L60 [soft] `simp-law-injection` in `simp-declaration add_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L65 [soft] `law-field-locker` in `structure-field PositiveMeasure.add` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [soft] `simp-law-injection` in `simp-declaration scale_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L81 [advisory] `existential-packaging` in `def Z` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L85 [soft] `simp-law-injection` in `simp-declaration Z_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L120 [soft] `simp-law-injection` in `simp-declaration normalize_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L123 [soft] `skeletal-proof` in `lemma Z_normalize` — proof appears to close via minimal tactic one-liner
  - L153 [advisory] `local-hypothesis-injection` in `lemma gklTerm_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L165 [advisory] `local-hypothesis-injection` in `lemma gklTerm_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L168 [advisory] `local-hypothesis-injection` in `lemma gklTerm_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L170 [advisory] `local-hypothesis-injection` in `lemma gklTerm_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L171 [advisory] `local-hypothesis-injection` in `lemma gklTerm_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L173 [advisory] `local-hypothesis-injection` in `lemma gklTerm_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L177 [soft] `skeletal-proof` in `lemma gklTerm_pos_of_ne` — proof appears to close via minimal tactic one-liner
  - L181 [advisory] `local-hypothesis-injection` in `lemma gklTerm_pos_of_ne` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L184 [advisory] `local-hypothesis-injection` in `lemma gklTerm_pos_of_ne` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L186 [advisory] `local-hypothesis-injection` in `lemma gklTerm_pos_of_ne` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L188 [advisory] `local-hypothesis-injection` in `lemma gklTerm_pos_of_ne` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L190 [advisory] `local-hypothesis-injection` in `lemma gklTerm_pos_of_ne` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L191 [advisory] `local-hypothesis-injection` in `lemma gklTerm_pos_of_ne` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L195 [advisory] `local-hypothesis-injection` in `lemma gklTerm_pos_of_ne` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L198 [advisory] `local-hypothesis-injection` in `lemma gklTerm_pos_of_ne` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L206 [advisory] `local-hypothesis-injection` in `lemma gklTerm_eq_zero_iff` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L222 [soft] `skeletal-proof` in `theorem generalizedKL_eq_zero_iff` — proof appears to close via minimal tactic one-liner
  - L228 [advisory] `local-hypothesis-injection` in `theorem generalizedKL_eq_zero_iff` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L230 [advisory] `local-hypothesis-injection` in `theorem generalizedKL_eq_zero_iff` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

