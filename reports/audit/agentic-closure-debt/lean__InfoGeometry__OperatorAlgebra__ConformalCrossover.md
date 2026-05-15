# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:11.010662+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ConformalCrossover.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **19**
- Hard: **0**
- Soft: **10**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ConformalCrossover.lean` | `advisory` | 29 | 0 | 10 | 9 | 19 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ConformalCrossover.lean`
- module: `InfoGeometry.OperatorAlgebra.ConformalCrossover`
- status: `advisory`
- debt_score: `29`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L36 [soft] `law-field-locker` in `structure-field ConformalCrossoverDatum.theta_involutive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L40 [soft] `law-field-locker` in `structure-field ConformalCrossoverDatum.Null` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field ConformalCrossoverDatum.theta_preserves_null` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `law-field-locker` in `structure-field ConformalCrossoverDatum.null_smul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L61 [advisory] `existential-packaging` in `def IsProjectivelyFixed` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L100 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L111 [soft] `skeletal-proof` in `theorem sameRay_refl` — proof appears to close via minimal tactic one-liner
  - L133 [soft] `skeletal-proof` in `theorem span_singleton_smul_eq` — proof appears to close via minimal tactic one-liner
  - L147 [advisory] `local-hypothesis-injection` in `theorem span_singleton_smul_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L157 [advisory] `local-hypothesis-injection` in `theorem span_singleton_smul_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L186 [advisory] `local-hypothesis-injection` in `def crossover` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L196 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L198 [soft] `skeletal-proof` in `theorem crossover_generator` — proof appears to close via minimal tactic one-liner
  - L265 [advisory] `local-hypothesis-injection` in `def rescale` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L297 [soft] `law-field-locker` in `structure-field GenesisContext.seedMap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L299 [soft] `law-field-locker` in `structure-field GenesisContext.seed_nonzero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L314 [soft] `law-field-locker` in `structure-field GenesisSeed.seed_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

