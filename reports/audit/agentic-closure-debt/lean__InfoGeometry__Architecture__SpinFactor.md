# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:31.492527+00:00`
Root: `lean/InfoGeometry/Architecture/SpinFactor.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **3**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Architecture/SpinFactor.lean` | `advisory` | 8 | 0 | 3 | 2 | 5 |

## Findings by file

### `lean/InfoGeometry/Architecture/SpinFactor.lean`
- module: `InfoGeometry.Architecture.SpinFactor`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L26 [soft] `skeletal-proof` in `lemma spinFactor_poly_identity` — proof appears to close via minimal tactic one-liner
  - L33 [advisory] `local-hypothesis-injection` in `lemma spinFactor_poly_identity` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L46 [soft] `skeletal-proof` in `lemma spinFactorPotential_well_defined` — proof appears to close via minimal tactic one-liner
  - L53 [soft] `simp-law-injection` in `simp-declaration spinFactorPotential_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

