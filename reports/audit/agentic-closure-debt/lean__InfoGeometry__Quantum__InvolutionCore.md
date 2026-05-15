# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:35.326526+00:00`
Root: `lean/InfoGeometry/Quantum/InvolutionCore.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **7**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Quantum/InvolutionCore.lean` | `advisory` | 15 | 0 | 7 | 1 | 8 |

## Findings by file

### `lean/InfoGeometry/Quantum/InvolutionCore.lean`
- module: `InfoGeometry.Quantum.InvolutionCore`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L21 [soft] `law-field-locker` in `structure-field InvolutionCore.J` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L22 [soft] `law-field-locker` in `structure-field InvolutionCore.eps` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L23 [soft] `law-field-locker` in `structure-field InvolutionCore.J_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L24 [soft] `law-field-locker` in `structure-field InvolutionCore.eps_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L36 [soft] `simp-law-injection` in `simp-declaration je_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L39 [soft] `simp-law-injection` in `simp-declaration J_sq_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L43 [soft] `simp-law-injection` in `simp-declaration eps_sq_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

