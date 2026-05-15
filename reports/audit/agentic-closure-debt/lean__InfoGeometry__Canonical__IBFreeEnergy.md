# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:17.379738+00:00`
Root: `lean/InfoGeometry/Canonical/IBFreeEnergy.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **4**
- Hard: **0**
- Soft: **1**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/IBFreeEnergy.lean` | `advisory` | 5 | 0 | 1 | 3 | 4 |

## Findings by file

### `lean/InfoGeometry/Canonical/IBFreeEnergy.lean`
- module: `InfoGeometry.Canonical.IBFreeEnergy`
- status: `advisory`
- debt_score: `5`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L25 [soft] `simp-law-injection` in `simp-declaration klDivENN_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L29 [advisory] `existential-packaging` in `lemma klDiv_nonneg` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L38 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

