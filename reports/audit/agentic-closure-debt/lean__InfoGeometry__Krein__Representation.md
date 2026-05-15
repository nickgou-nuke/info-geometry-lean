# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:54.281601+00:00`
Root: `lean/InfoGeometry/Krein/Representation.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **2**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Krein/Representation.lean` | `advisory` | 8 | 0 | 2 | 4 | 6 |

## Findings by file

### `lean/InfoGeometry/Krein/Representation.lean`
- module: `InfoGeometry.Krein.Representation`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L43 [soft] `skeletal-proof` in `lemma cl11RepLin_sq` — proof appears to close via minimal tactic one-liner
  - L47 [advisory] `local-hypothesis-injection` in `lemma cl11RepLin_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L48 [advisory] `local-hypothesis-injection` in `lemma cl11RepLin_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L51 [advisory] `local-hypothesis-injection` in `lemma cl11RepLin_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L87 [soft] `simp-law-injection` in `simp-declaration cl11Rep_` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

