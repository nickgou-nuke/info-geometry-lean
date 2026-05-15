# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:16.619994+00:00`
Root: `lean/InfoGeometry/Clifford/Cl11Matrix.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **3**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Clifford/Cl11Matrix.lean` | `advisory` | 11 | 0 | 3 | 5 | 8 |

## Findings by file

### `lean/InfoGeometry/Clifford/Cl11Matrix.lean`
- module: `InfoGeometry.Clifford.Cl11Matrix`
- status: `advisory`
- debt_score: `11`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L33 [soft] `simp-law-injection` in `simp-declaration q11_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L96 [soft] `skeletal-proof` in `lemma cl11ToMat_preimage` — proof appears to close via minimal tactic one-liner
  - L99 [advisory] `local-hypothesis-injection` in `lemma cl11ToMat_preimage` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L100 [advisory] `local-hypothesis-injection` in `lemma cl11ToMat_preimage` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L102 [advisory] `local-hypothesis-injection` in `lemma cl11ToMat_preimage` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L108 [soft] `skeletal-proof` in `lemma finrank_mat2` — proof appears to close via minimal tactic one-liner
  - L125 [advisory] `local-hypothesis-injection` in `def cl11EquivMat` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

