# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:54.002088+00:00`
Root: `lean/InfoGeometry/Krein/Prelude.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **24**
- Hard: **0**
- Soft: **23**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Krein/Prelude.lean` | `advisory` | 47 | 0 | 23 | 1 | 24 |

## Findings by file

### `lean/InfoGeometry/Krein/Prelude.lean`
- module: `InfoGeometry.Krein.Prelude`
- status: `advisory`
- debt_score: `47`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L19 [soft] `simp-law-injection` in `simp-declaration chiralityOperator_eq_modular_j` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L22 [soft] `simp-law-injection` in `simp-declaration complexStructureOperator_eq_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L46 [soft] `simp-law-injection` in `simp-declaration chiralityProjPlus_eq_gradePlusProj` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L49 [soft] `simp-law-injection` in `simp-declaration chiralityProjMinus_eq_gradeMinusProj` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L52 [soft] `simp-law-injection` in `simp-declaration chiralityProjPlus_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L56 [soft] `simp-law-injection` in `simp-declaration chiralityProjMinus_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L60 [soft] `skeletal-proof` in `lemma chiralityProjPlus_idempotent` — proof appears to close via minimal tactic one-liner
  - L65 [soft] `skeletal-proof` in `lemma chiralityProjMinus_idempotent` — proof appears to close via minimal tactic one-liner
  - L86 [soft] `skeletal-proof` in `lemma chiralityProjPlus_add_chiralityProjMinus` — proof appears to close via minimal tactic one-liner
  - L108 [soft] `law-field-locker` in `structure-field VacuumChoice.imag` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L109 [soft] `law-field-locker` in `structure-field VacuumChoice.imag_sq_neg_id` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L156 [soft] `skeletal-proof` in `theorem vacuumChoice_switch_swaps_polarizations_plus` — proof appears to close via minimal tactic one-liner
  - L162 [soft] `skeletal-proof` in `theorem vacuumChoice_switch_swaps_polarizations_minus` — proof appears to close via minimal tactic one-liner
  - L183 [soft] `simp-law-injection` in `simp-declaration chiralityOperator_eq_modular_j` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L187 [soft] `simp-law-injection` in `simp-declaration complexStructureOperator_eq_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L194 [soft] `skeletal-proof` in `theorem complex_i_sq_neg_id` — proof appears to close via minimal tactic one-liner
  - L199 [soft] `skeletal-proof` in `theorem complex_i_isComplexStructureOp` — proof appears to close via minimal tactic one-liner
  - L209 [soft] `simp-law-injection` in `simp-declaration chiralityProjPlus_eq_gradePlusProj` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L213 [soft] `simp-law-injection` in `simp-declaration chiralityProjMinus_eq_gradeMinusProj` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L243 [soft] `skeletal-proof` in `theorem vacuumChoice_switch_swaps_splits_plus` — proof appears to close via minimal tactic one-liner
  - L248 [soft] `skeletal-proof` in `theorem vacuumChoice_switch_swaps_splits_minus` — proof appears to close via minimal tactic one-liner
  - L253 [soft] `skeletal-proof` in `theorem vacuumChoice_switch_swaps_polarizations_plus` — proof appears to close via minimal tactic one-liner
  - L258 [soft] `skeletal-proof` in `theorem vacuumChoice_switch_swaps_polarizations_minus` — proof appears to close via minimal tactic one-liner

