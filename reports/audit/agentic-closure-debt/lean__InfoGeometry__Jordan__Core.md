# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:45.358178+00:00`
Root: `lean/InfoGeometry/Jordan/Core.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **14**
- Hard: **0**
- Soft: **13**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Jordan/Core.lean` | `advisory` | 27 | 0 | 13 | 1 | 14 |

## Findings by file

### `lean/InfoGeometry/Jordan/Core.lean`
- module: `InfoGeometry.Jordan.Core`
- status: `advisory`
- debt_score: `27`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L14 [soft] `law-field-locker` in `class-field JordanAlgebra.jordanProd` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L15 [soft] `law-field-locker` in `class-field JordanAlgebra.add_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L16 [soft] `law-field-locker` in `class-field JordanAlgebra.smul_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L17 [soft] `law-field-locker` in `class-field JordanAlgebra.comm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L18 [soft] `law-field-locker` in `class-field JordanAlgebra.jordan_identity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L31 [soft] `simp-law-injection` in `simp-declaration jordanProd_comm` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L35 [soft] `simp-law-injection` in `simp-declaration jordanProd_add_left` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L40 [soft] `simp-law-injection` in `simp-declaration jordanProd_smul_left` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L45 [soft] `simp-law-injection` in `simp-declaration jordanProd_add_right` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L50 [soft] `simp-law-injection` in `simp-declaration jordanProd_smul_right` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L55 [soft] `simp-law-injection` in `simp-declaration jordanProd_zero_left` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L57 [soft] `skeletal-proof` in `lemma jordanProd_zero_left` — proof appears to close via minimal tactic one-liner
  - L60 [soft] `simp-law-injection` in `simp-declaration jordanProd_zero_right` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

