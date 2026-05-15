# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:00.734922+00:00`
Root: `lean/InfoGeometry/MaxEnt/Optimality.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **0**
- Advisory: **15**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/MaxEnt/Optimality.lean` | `advisory` | 15 | 0 | 0 | 15 | 15 |

## Findings by file

### `lean/InfoGeometry/MaxEnt/Optimality.lean`
- module: `InfoGeometry.MaxEnt.Optimality`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [advisory] `local-hypothesis-injection` in `def probDistOfSimplex` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L37 [advisory] `local-hypothesis-injection` in `def probDistOfSimplex` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L54 [advisory] `local-hypothesis-injection` in `def gibbsDist` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L57 [advisory] `local-hypothesis-injection` in `def gibbsDist` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L131 [advisory] `local-hypothesis-injection` in `lemma entropy_gibbs_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L152 [advisory] `local-hypothesis-injection` in `theorem max_ent_lagrange_multiplier_gibbs` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L157 [advisory] `local-hypothesis-injection` in `theorem max_ent_lagrange_multiplier_gibbs` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L166 [advisory] `local-hypothesis-injection` in `theorem max_ent_lagrange_multiplier_gibbs` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L168 [advisory] `local-hypothesis-injection` in `theorem max_ent_lagrange_multiplier_gibbs` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L169 [advisory] `local-hypothesis-injection` in `theorem max_ent_lagrange_multiplier_gibbs` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L170 [advisory] `local-hypothesis-injection` in `theorem max_ent_lagrange_multiplier_gibbs` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L190 [advisory] `local-hypothesis-injection` in `theorem max_ent_lagrange_multiplier_gibbs` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L193 [advisory] `local-hypothesis-injection` in `theorem max_ent_lagrange_multiplier_gibbs` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L195 [advisory] `local-hypothesis-injection` in `theorem max_ent_lagrange_multiplier_gibbs` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

