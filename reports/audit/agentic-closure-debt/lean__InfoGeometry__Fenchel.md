# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:35.186111+00:00`
Root: `lean/InfoGeometry/Fenchel.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **7**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Fenchel.lean` | `advisory` | 17 | 0 | 7 | 3 | 10 |

## Findings by file

### `lean/InfoGeometry/Fenchel.lean`
- module: `InfoGeometry.Fenchel`
- status: `advisory`
- debt_score: `17`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L23 [soft] `skeletal-proof` in `lemma bregmanDiv_three_point` — proof appears to close via minimal tactic one-liner
  - L33 [soft] `skeletal-proof` in `lemma bregmanDiv_pythagorean_ineq` — proof appears to close via minimal tactic one-liner
  - L130 [soft] `law-field-locker` in `structure-field DualFlatPotential.primal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L131 [soft] `law-field-locker` in `structure-field DualFlatPotential.dual` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L159 [soft] `skeletal-proof` in `lemma fenchel_legendre_equivalence` — proof appears to close via minimal tactic one-liner
  - L185 [advisory] `local-hypothesis-injection` in `lemma fenchel_legendre_equivalence` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L187 [advisory] `local-hypothesis-injection` in `lemma fenchel_legendre_equivalence` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L255 [soft] `skeletal-proof` in `lemma kernelClosure_monotone` — proof appears to close via minimal tactic one-liner
  - L266 [soft] `skeletal-proof` in `lemma kernel_idempotent` — proof appears to close via minimal tactic one-liner

