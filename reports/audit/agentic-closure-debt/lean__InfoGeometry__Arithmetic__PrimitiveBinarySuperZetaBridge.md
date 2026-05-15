# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:33.161163+00:00`
Root: `lean/InfoGeometry/Arithmetic/PrimitiveBinarySuperZetaBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **4**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Arithmetic/PrimitiveBinarySuperZetaBridge.lean` | `advisory` | 12 | 0 | 4 | 4 | 8 |

## Findings by file

### `lean/InfoGeometry/Arithmetic/PrimitiveBinarySuperZetaBridge.lean`
- module: `InfoGeometry.Arithmetic.PrimitiveBinarySuperZetaBridge`
- status: `advisory`
- debt_score: `12`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L39 [soft] `law-field-locker` in `structure-field FinitePrimeBitLattice.prime` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L40 [soft] `law-field-locker` in `structure-field FinitePrimeBitLattice.prime_isPrime` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L46 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L208 [soft] `skeletal-proof` in `theorem profileLe_of_bitInteger_dvd` — proof appears to close via minimal tactic one-liner
  - L241 [advisory] `local-hypothesis-injection` in `theorem profileLe_of_bitInteger_dvd` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L245 [advisory] `local-hypothesis-injection` in `theorem profileLe_of_bitInteger_dvd` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L293 [soft] `law-field-locker` in `structure-field PrimitiveBinarySupport.nontrivial` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

