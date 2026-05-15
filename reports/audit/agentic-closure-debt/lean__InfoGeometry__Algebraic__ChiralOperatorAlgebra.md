# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:27.679970+00:00`
Root: `lean/InfoGeometry/Algebraic/ChiralOperatorAlgebra.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **14**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Algebraic/ChiralOperatorAlgebra.lean` | `advisory` | 29 | 0 | 14 | 1 | 15 |

## Findings by file

### `lean/InfoGeometry/Algebraic/ChiralOperatorAlgebra.lean`
- module: `InfoGeometry.Algebraic.ChiralOperatorAlgebra`
- status: `advisory`
- debt_score: `29`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [soft] `law-field-locker` in `structure-field ChiralOperatorAlgebra.modularBoost` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L37 [soft] `law-field-locker` in `structure-field ChiralOperatorAlgebra.leftChiralCharge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L40 [soft] `law-field-locker` in `structure-field ChiralOperatorAlgebra.rightChiralCharge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field ChiralOperatorAlgebra.modularHamiltonian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [soft] `simp-law-injection` in `simp-declaration canonical_chiralParity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L76 [soft] `skeletal-proof` in `theorem canonical_chiralParity` — proof appears to close via minimal tactic one-liner
  - L80 [soft] `simp-law-injection` in `simp-declaration canonical_modularBoost` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L82 [soft] `skeletal-proof` in `theorem canonical_modularBoost` — proof appears to close via minimal tactic one-liner
  - L87 [soft] `simp-law-injection` in `simp-declaration canonical_leftChiralCharge` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L89 [soft] `skeletal-proof` in `theorem canonical_leftChiralCharge` — proof appears to close via minimal tactic one-liner
  - L94 [soft] `simp-law-injection` in `simp-declaration canonical_rightChiralCharge` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L96 [soft] `skeletal-proof` in `theorem canonical_rightChiralCharge` — proof appears to close via minimal tactic one-liner
  - L101 [soft] `simp-law-injection` in `simp-declaration canonical_modularHamiltonian` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L103 [soft] `skeletal-proof` in `theorem canonical_modularHamiltonian` — proof appears to close via minimal tactic one-liner

