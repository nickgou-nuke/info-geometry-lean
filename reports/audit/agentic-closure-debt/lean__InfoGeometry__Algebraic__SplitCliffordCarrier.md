# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:29.666542+00:00`
Root: `lean/InfoGeometry/Algebraic/SplitCliffordCarrier.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **5**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Algebraic/SplitCliffordCarrier.lean` | `advisory` | 11 | 0 | 5 | 1 | 6 |

## Findings by file

### `lean/InfoGeometry/Algebraic/SplitCliffordCarrier.lean`
- module: `InfoGeometry.Algebraic.SplitCliffordCarrier`
- status: `advisory`
- debt_score: `11`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L21 [soft] `simp-law-injection` in `simp-declaration splitCliffordVector_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L23 [soft] `skeletal-proof` in `theorem splitCliffordVector_sq` — proof appears to close via minimal tactic one-liner
  - L28 [soft] `simp-law-injection` in `simp-declaration splitClifford_posBasis_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L36 [soft] `simp-law-injection` in `simp-declaration splitClifford_negBasis_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L64 [soft] `law-field-locker` in `structure-field SplitVolumeData.volume_sq_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

