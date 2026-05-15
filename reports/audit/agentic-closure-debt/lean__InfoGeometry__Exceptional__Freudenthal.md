# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:27.807764+00:00`
Root: `lean/InfoGeometry/Exceptional/Freudenthal.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **11**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Exceptional/Freudenthal.lean` | `advisory` | 24 | 0 | 11 | 2 | 13 |

## Findings by file

### `lean/InfoGeometry/Exceptional/Freudenthal.lean`
- module: `InfoGeometry.Exceptional.Freudenthal`
- status: `advisory`
- debt_score: `24`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L28 [soft] `law-field-locker` in `structure-field CubicJordanDatum.traceBilin` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L30 [soft] `law-field-locker` in `structure-field CubicJordanDatum.trace_comm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L33 [soft] `law-field-locker` in `structure-field CubicJordanDatum.normCubic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L36 [soft] `law-field-locker` in `structure-field CubicJordanDatum.adjointQuad` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L39 [soft] `law-field-locker` in `structure-field CubicJordanDatum.normTrilin` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L50 [soft] `law-field-locker` in `structure-field CubicJordanDatum.normTrilin_self` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L61 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L122 [soft] `simp-law-injection` in `simp-declaration symplectic_form_alternating` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L164 [soft] `law-field-locker` in `structure-field TKKClosureDatum.op_0_0` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L167 [soft] `law-field-locker` in `structure-field TKKClosureDatum.op_0_minus1` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L170 [soft] `law-field-locker` in `structure-field TKKClosureDatum.op_0_plus1` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L173 [soft] `law-field-locker` in `structure-field TKKClosureDatum.op_minus1_plus1` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

