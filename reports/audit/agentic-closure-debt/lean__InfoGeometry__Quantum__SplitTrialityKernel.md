# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:36.977273+00:00`
Root: `lean/InfoGeometry/Quantum/SplitTrialityKernel.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **36**
- Hard: **0**
- Soft: **16**
- Advisory: **20**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Quantum/SplitTrialityKernel.lean` | `advisory` | 52 | 0 | 16 | 20 | 36 |

## Findings by file

### `lean/InfoGeometry/Quantum/SplitTrialityKernel.lean`
- module: `InfoGeometry.Quantum.SplitTrialityKernel`
- status: `advisory`
- debt_score: `52`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L33 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L35 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L47 [soft] `law-field-locker` in `structure-field SplitTrialityKernel.vectorToLeftSpinor` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [soft] `law-field-locker` in `structure-field SplitTrialityKernel.vectorToRightSpinor` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `law-field-locker` in `structure-field SplitTrialityKernel.left_nilpotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L50 [soft] `law-field-locker` in `structure-field SplitTrialityKernel.right_nilpotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [soft] `law-field-locker` in `structure-field SplitTrialityKernel.right_comp_left_eq_plus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [soft] `law-field-locker` in `structure-field SplitTrialityKernel.left_comp_right_eq_minus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L69 [soft] `skeletal-proof` in `theorem informationalDiracSquare_eq_id` — proof appears to close via minimal tactic one-liner
  - L88 [soft] `simp-law-injection` in `simp-declaration trialitySupercharge_sq_eq_id` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L97 [soft] `skeletal-proof` in `theorem trialitySupercharge_sq_eq_anticommutator` — proof appears to close via minimal tactic one-liner
  - L120 [soft] `skeletal-proof` in `theorem trialitySupercharge_comp_plus_eq_left` — proof appears to close via minimal tactic one-liner
  - L123 [advisory] `local-hypothesis-injection` in `theorem trialitySupercharge_comp_plus_eq_left` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L138 [advisory] `local-hypothesis-injection` in `theorem trialitySupercharge_comp_plus_eq_left` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L152 [advisory] `local-hypothesis-injection` in `theorem trialitySupercharge_comp_plus_eq_left` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L178 [advisory] `local-hypothesis-injection` in `theorem trialitySupercharge_comp_minus_eq_right` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L191 [advisory] `local-hypothesis-injection` in `theorem trialitySupercharge_comp_minus_eq_right` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L206 [advisory] `local-hypothesis-injection` in `theorem trialitySupercharge_comp_minus_eq_right` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L233 [advisory] `local-hypothesis-injection` in `theorem plus_comp_trialitySupercharge_eq_right` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L246 [advisory] `local-hypothesis-injection` in `theorem plus_comp_trialitySupercharge_eq_right` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L261 [advisory] `local-hypothesis-injection` in `theorem plus_comp_trialitySupercharge_eq_right` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L285 [soft] `skeletal-proof` in `theorem minus_comp_trialitySupercharge_eq_left` — proof appears to close via minimal tactic one-liner
  - L288 [advisory] `local-hypothesis-injection` in `theorem minus_comp_trialitySupercharge_eq_left` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L303 [advisory] `local-hypothesis-injection` in `theorem minus_comp_trialitySupercharge_eq_left` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L317 [advisory] `local-hypothesis-injection` in `theorem minus_comp_trialitySupercharge_eq_left` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L355 [soft] `skeletal-proof` in `theorem k_acts_as_imaginary` — proof appears to close via minimal tactic one-liner
  - L381 [soft] `simp-law-injection` in `simp-declaration vectorToLeftSpinor_apply_to_doubled` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L388 [soft] `simp-law-injection` in `simp-declaration vectorToRightSpinor_apply_to_doubled` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L401 [advisory] `local-hypothesis-injection` in `theorem vectorToLeftSpinor_nilpotent` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L412 [advisory] `local-hypothesis-injection` in `theorem vectorToRightSpinor_nilpotent` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L429 [advisory] `local-hypothesis-injection` in `theorem vectorToRightSpinor_comp_vectorToLeftSpinor_eq_plusProj` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L449 [advisory] `local-hypothesis-injection` in `theorem vectorToLeftSpinor_comp_vectorToRightSpinor_eq_minusProj` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L479 [advisory] `local-hypothesis-injection` in `theorem trialitySupercharge_eq_modularJ` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L517 [soft] `simp-law-injection` in `simp-declaration informationalDiracSquare_eq_id` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L523 [soft] `simp-law-injection` in `simp-declaration paritySupercharge_hamiltonian_eq_id` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

