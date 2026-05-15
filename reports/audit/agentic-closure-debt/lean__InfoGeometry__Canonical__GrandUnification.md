# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:12.591040+00:00`
Root: `lean/InfoGeometry/Canonical/GrandUnification.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **29**
- Hard: **0**
- Soft: **13**
- Advisory: **16**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/GrandUnification.lean` | `advisory` | 42 | 0 | 13 | 16 | 29 |

## Findings by file

### `lean/InfoGeometry/Canonical/GrandUnification.lean`
- module: `InfoGeometry.Canonical.GrandUnification`
- status: `advisory`
- debt_score: `42`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L21 [soft] `law-field-locker` in `structure-field JordanKKTData.detJ` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L22 [soft] `law-field-locker` in `structure-field JordanKKTData.detJ_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L23 [soft] `law-field-locker` in `structure-field JordanKKTData.gradK` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L24 [soft] `law-field-locker` in `structure-field JordanKKTData.has_gradient` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L26 [soft] `law-field-locker` in `structure-field JordanKKTData.has_hessian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L28 [soft] `law-field-locker` in `structure-field JordanKKTData.dbregman_pos_of_ne` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L42 [advisory] `existential-packaging` in `def dualPotential` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L54 [soft] `simp-law-injection` in `simp-declaration DBregman_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L58 [soft] `simp-law-injection` in `simp-declaration hasFDerivAt_K` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L74 [soft] `simp-law-injection` in `simp-declaration DBregman_eq_zero_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L82 [advisory] `local-hypothesis-injection` in `theorem DBregman_eq_zero_iff` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L97 [advisory] `existential-packaging` in `theorem fenchel_young_equality` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L97 [soft] `skeletal-proof` in `theorem fenchel_young_equality` — proof appears to close via minimal tactic one-liner
  - L106 [advisory] `local-hypothesis-injection` in `theorem fenchel_young_equality` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L116 [advisory] `local-hypothesis-injection` in `theorem fenchel_young_equality` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L118 [advisory] `local-hypothesis-injection` in `theorem fenchel_young_equality` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L121 [advisory] `local-hypothesis-injection` in `theorem fenchel_young_equality` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L123 [advisory] `local-hypothesis-injection` in `theorem fenchel_young_equality` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L125 [advisory] `local-hypothesis-injection` in `theorem fenchel_young_equality` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L126 [advisory] `local-hypothesis-injection` in `theorem fenchel_young_equality` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L130 [soft] `simp-law-injection` in `simp-declaration dualPotential_grad_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L144 [advisory] `existential-packaging` in `theorem mixed_bregman_identity` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L158 [advisory] `existential-packaging` in `theorem dual_potential_mixed_identity` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L174 [soft] `skeletal-proof` in `theorem three_point_law` — proof appears to close via minimal tactic one-liner
  - L177 [advisory] `local-hypothesis-injection` in `theorem three_point_law` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L238 [soft] `skeletal-proof` in `theorem projection_unique` — proof appears to close via minimal tactic one-liner
  - L243 [advisory] `local-hypothesis-injection` in `theorem projection_unique` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L246 [advisory] `local-hypothesis-injection` in `theorem projection_unique` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

