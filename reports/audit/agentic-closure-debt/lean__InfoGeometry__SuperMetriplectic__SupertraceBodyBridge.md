# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:44.282157+00:00`
Root: `lean/InfoGeometry/SuperMetriplectic/SupertraceBodyBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **11**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/SuperMetriplectic/SupertraceBodyBridge.lean` | `advisory` | 23 | 0 | 11 | 1 | 12 |

## Findings by file

### `lean/InfoGeometry/SuperMetriplectic/SupertraceBodyBridge.lean`
- module: `InfoGeometry.SuperMetriplectic.SupertraceBodyBridge`
- status: `advisory`
- debt_score: `23`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L41 [soft] `law-field-locker` in `structure-field SupertraceFisherShadow.ordinaryTraceQuadratic_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L44 [soft] `law-field-locker` in `structure-field SupertraceFisherShadow.supertraceQuadratic_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `law-field-locker` in `structure-field SupertraceFisherShadow.bodyFisherQuadratic_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L50 [soft] `law-field-locker` in `structure-field SupertraceFisherShadow.bodyFisherQuadratic_nonnegative` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L120 [soft] `law-field-locker` in `structure-field ZornSupertraceFisherBridge.zornTotal_eq_bodyFisher` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L161 [soft] `law-field-locker` in `structure-field SplitParitySupertraceShadow.parity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L162 [soft] `law-field-locker` in `structure-field SplitParitySupertraceShadow.supertraceReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L163 [soft] `law-field-locker` in `structure-field SplitParitySupertraceShadow.superBerezinianReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L164 [soft] `law-field-locker` in `structure-field SplitParitySupertraceShadow.supervolumePotential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L165 [soft] `simp-law-injection` in `simp-declaration parity_comp_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L170 [soft] `simp-law-injection` in `simp-declaration supervolumePotential_eq_neg_log_superBerezinian` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

