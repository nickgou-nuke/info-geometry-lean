# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:12.327626+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/CrossoverResidue.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **35**
- Hard: **0**
- Soft: **24**
- Advisory: **11**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/CrossoverResidue.lean` | `advisory` | 59 | 0 | 24 | 11 | 35 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/CrossoverResidue.lean`
- module: `InfoGeometry.OperatorAlgebra.CrossoverResidue`
- status: `advisory`
- debt_score: `59`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L48 [soft] `simp-law-injection` in `simp-declaration sign_left` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L50 [soft] `skeletal-proof` in `theorem sign_left` — proof appears to close via minimal tactic one-liner
  - L53 [soft] `simp-law-injection` in `simp-declaration sign_right` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L55 [soft] `skeletal-proof` in `theorem sign_right` — proof appears to close via minimal tactic one-liner
  - L58 [soft] `simp-law-injection` in `simp-declaration flip_left` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L60 [soft] `skeletal-proof` in `theorem flip_left` — proof appears to close via minimal tactic one-liner
  - L63 [soft] `simp-law-injection` in `simp-declaration flip_right` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L65 [soft] `skeletal-proof` in `theorem flip_right` — proof appears to close via minimal tactic one-liner
  - L68 [soft] `simp-law-injection` in `simp-declaration flip_flip` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L74 [soft] `simp-law-injection` in `simp-declaration sign_flip` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L103 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L136 [soft] `simp-law-injection` in `simp-declaration crossover_weight` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L138 [soft] `skeletal-proof` in `theorem crossover_weight` — proof appears to close via minimal tactic one-liner
  - L141 [soft] `simp-law-injection` in `simp-declaration crossover_chirality` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L143 [soft] `skeletal-proof` in `theorem crossover_chirality` — proof appears to close via minimal tactic one-liner
  - L167 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L185 [soft] `skeletal-proof` in `theorem chiralCharge_empty` — proof appears to close via minimal tactic one-liner
  - L190 [soft] `skeletal-proof` in `theorem chiralCharge_cons` — proof appears to close via minimal tactic one-liner
  - L199 [soft] `skeletal-proof` in `theorem chiralCharge_crossover` — proof appears to close via minimal tactic one-liner
  - L220 [soft] `skeletal-proof` in `theorem crossover_chirallyBalanced_iff` — proof appears to close via minimal tactic one-liner
  - L226 [advisory] `local-hypothesis-injection` in `theorem crossover_chirallyBalanced_iff` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L232 [advisory] `existential-packaging` in `theorem residue_mem_finite_support` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L232 [soft] `skeletal-proof` in `theorem residue_mem_finite_support` — proof appears to close via minimal tactic one-liner
  - L253 [advisory] `local-hypothesis-injection` in `theorem residue_mem_finite_support` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L277 [soft] `law-field-locker` in `structure-field ResolvedResidueSeed.orientation_matches` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L293 [soft] `law-field-locker` in `structure-field DivisorResolutionAudit.resolve` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L308 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L310 [advisory] `existential-packaging` in `theorem every_residue_has_smooth_seed` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L366 [soft] `law-field-locker` in `structure-field ChiralVorticityReadout.orientation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L367 [soft] `law-field-locker` in `structure-field ChiralVorticityReadout.vorticitySign` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L368 [soft] `law-field-locker` in `structure-field ChiralVorticityReadout.vorticitySign_eq_orientation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L375 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L395 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L398 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

