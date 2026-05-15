# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:39.602150+00:00`
Root: `lean/InfoGeometry/Singular/KreinNaturalFlow.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **9**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Singular/KreinNaturalFlow.lean` | `advisory` | 19 | 0 | 9 | 1 | 10 |

## Findings by file

### `lean/InfoGeometry/Singular/KreinNaturalFlow.lean`
- module: `InfoGeometry.Singular.KreinNaturalFlow`
- status: `advisory`
- debt_score: `19`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L38 [soft] `simp-law-injection` in `simp-declaration kreinAdjointH_involutive` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L44 [soft] `simp-law-injection` in `simp-declaration kreinAdjointH_comp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L51 [soft] `simp-law-injection` in `simp-declaration kreinAdjointH_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L84 [soft] `law-field-locker` in `structure-field SingularNaturalGradientFlow.G_pinv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L86 [soft] `law-field-locker` in `structure-field SingularNaturalGradientFlow.generator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L87 [soft] `law-field-locker` in `structure-field SingularNaturalGradientFlow.gen_def` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L88 [soft] `law-field-locker` in `structure-field SingularNaturalGradientFlow.D_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L91 [soft] `law-field-locker` in `structure-field SingularNaturalGradientFlow.transport_generator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L92 [soft] `law-field-locker` in `structure-field SingularNaturalGradientFlow.isometry` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

