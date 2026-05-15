# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:56.833283+00:00`
Root: `lean/InfoGeometry/LLM/MaskedTransformerBlock.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **4**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/LLM/MaskedTransformerBlock.lean` | `advisory` | 9 | 0 | 4 | 1 | 5 |

## Findings by file

### `lean/InfoGeometry/LLM/MaskedTransformerBlock.lean`
- module: `InfoGeometry.LLM.MaskedTransformerBlock`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L15 [soft] `law-field-locker` in `structure-field CausalMask.allow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L27 [soft] `law-field-locker` in `structure-field MaskedTransformerBlock.base` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L75 [soft] `simp-law-injection` in `simp-declaration maskedHeadWeight_of_not_allow` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L83 [soft] `simp-law-injection` in `simp-declaration maskedHeadWeight_of_allow` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

