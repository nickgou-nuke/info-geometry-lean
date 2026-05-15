# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:52.963113+00:00`
Root: `lean/SelfReference/Moebius.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **4**
- Hard: **0**
- Soft: **3**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/SelfReference/Moebius.lean` | `advisory` | 7 | 0 | 3 | 1 | 4 |

## Findings by file

### `lean/SelfReference/Moebius.lean`
- module: `SelfReference.Moebius`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L28 [soft] `law-field-locker` in `structure-field MoebiusLoop.toSector` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L29 [soft] `law-field-locker` in `structure-field MoebiusLoop.feed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L54 [soft] `simp-law-injection` in `simp-declaration moebius_parity_restored` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

