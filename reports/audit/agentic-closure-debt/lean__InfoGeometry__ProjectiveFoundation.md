# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:32.352044+00:00`
Root: `lean/InfoGeometry/ProjectiveFoundation.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **8**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/ProjectiveFoundation.lean` | `advisory` | 18 | 0 | 8 | 2 | 10 |

## Findings by file

### `lean/InfoGeometry/ProjectiveFoundation.lean`
- module: `InfoGeometry.ProjectiveFoundation`
- status: `advisory`
- debt_score: `18`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L47 [advisory] `existential-packaging` in `class KreinProjectiveCarrier` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L57 [soft] `law-field-locker` in `class-field KreinProjectiveCarrier.exists_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L58 [soft] `law-field-locker` in `class-field KreinProjectiveCarrier.exists_neg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L73 [soft] `law-field-locker` in `structure-field CoverRotorCocycle.projection` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [soft] `law-field-locker` in `structure-field CoverRotorCocycle.toFun` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L75 [soft] `law-field-locker` in `structure-field CoverRotorCocycle.map_one'` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L76 [soft] `law-field-locker` in `structure-field CoverRotorCocycle.map_mul'` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L86 [soft] `simp-law-injection` in `simp-declaration CoverRotorCocycle.map_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L95 [soft] `simp-law-injection` in `simp-declaration CoverRotorCocycle.map_mul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

