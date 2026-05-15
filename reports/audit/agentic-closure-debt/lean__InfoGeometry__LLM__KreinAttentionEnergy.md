# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:56.461016+00:00`
Root: `lean/InfoGeometry/LLM/KreinAttentionEnergy.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **4**
- Hard: **0**
- Soft: **2**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/LLM/KreinAttentionEnergy.lean` | `advisory` | 6 | 0 | 2 | 2 | 4 |

## Findings by file

### `lean/InfoGeometry/LLM/KreinAttentionEnergy.lean`
- module: `InfoGeometry.LLM.KreinAttentionEnergy`
- status: `advisory`
- debt_score: `6`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L18 [soft] `simp-law-injection` in `simp-declaration kreinInteractionEnergy_eq_neg_splitB11` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L21 [soft] `skeletal-proof` in `theorem kreinInteractionEnergy_eq_neg_splitB11` — proof appears to close via minimal tactic one-liner
  - L43 [advisory] `existential-packaging` in `theorem kreinAttentionWeights_sum_one` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

