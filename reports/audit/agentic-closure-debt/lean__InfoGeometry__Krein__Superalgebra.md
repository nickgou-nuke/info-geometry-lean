# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:54.885837+00:00`
Root: `lean/InfoGeometry/Krein/Superalgebra.lean`
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
| `lean/InfoGeometry/Krein/Superalgebra.lean` | `advisory` | 17 | 0 | 7 | 3 | 10 |

## Findings by file

### `lean/InfoGeometry/Krein/Superalgebra.lean`
- module: `InfoGeometry.Krein.Superalgebra`
- status: `advisory`
- debt_score: `17`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L25 [soft] `skeletal-proof` in `lemma comm_eq_lie` — proof appears to close via minimal tactic one-liner
  - L27 [soft] `simp-law-injection` in `simp-declaration gradeConj_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L32 [soft] `simp-law-injection` in `simp-declaration gradeConj_neg` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L37 [soft] `simp-law-injection` in `simp-declaration gradeConj_sub` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L41 [soft] `simp-law-injection` in `simp-declaration gradeConj_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L75 [soft] `skeletal-proof` in `lemma evenPart_eq_of_isEven` — proof appears to close via minimal tactic one-liner
  - L80 [advisory] `local-hypothesis-injection` in `lemma evenPart_eq_of_isEven` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L95 [soft] `skeletal-proof` in `lemma oddPart_eq_of_isOdd` — proof appears to close via minimal tactic one-liner
  - L100 [advisory] `local-hypothesis-injection` in `lemma oddPart_eq_of_isOdd` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

