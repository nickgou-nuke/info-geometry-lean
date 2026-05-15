# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:37.460211+00:00`
Root: `lean/InfoGeometry/Geometry/FiniteMatrixResolventKernel.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **6**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Geometry/FiniteMatrixResolventKernel.lean` | `advisory` | 16 | 0 | 6 | 4 | 10 |

## Findings by file

### `lean/InfoGeometry/Geometry/FiniteMatrixResolventKernel.lean`
- module: `InfoGeometry.Geometry.FiniteMatrixResolventKernel`
- status: `advisory`
- debt_score: `16`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L44 [soft] `law-field-locker` in `structure-field MatrixResolventKernel.diff_mul_kernel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `law-field-locker` in `structure-field MatrixResolventKernel.kernel_mul_diff` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L67 [soft] `skeletal-proof` in `theorem kernel_unique` — proof appears to close via minimal tactic one-liner
  - L130 [soft] `simp-law-injection` in `simp-declaration matrixResolventKernelOfUnit_kernel` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L133 [soft] `skeletal-proof` in `theorem matrixResolventKernelOfUnit_kernel` — proof appears to close via minimal tactic one-liner
  - L200 [soft] `skeletal-proof` in `theorem scalarOneByOneResolventKernel_entry` — proof appears to close via minimal tactic one-liner
  - L251 [advisory] `existential-packaging` in `def ScalarOneByOneResolventOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L263 [advisory] `existential-packaging` in `def MatrixResolventFromUnitOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

