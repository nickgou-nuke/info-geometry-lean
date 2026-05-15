# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:20.398405+00:00`
Root: `lean/InfoGeometry/Clifford/TowerMatrix.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **2**
- Advisory: **11**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Clifford/TowerMatrix.lean` | `advisory` | 15 | 0 | 2 | 11 | 13 |

## Findings by file

### `lean/InfoGeometry/Clifford/TowerMatrix.lean`
- module: `InfoGeometry.Clifford.TowerMatrix`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [advisory] `local-hypothesis-injection` in `lemma Jn_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L40 [advisory] `local-hypothesis-injection` in `lemma Jn_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L46 [soft] `skeletal-proof` in `lemma cartan_involutive` — proof appears to close via minimal tactic one-liner
  - L53 [advisory] `local-hypothesis-injection` in `lemma cartan_involutive` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L54 [advisory] `local-hypothesis-injection` in `lemma cartan_involutive` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L72 [soft] `skeletal-proof` in `lemma cartan_inv_of_isUnit` — proof appears to close via minimal tactic one-liner
  - L82 [advisory] `local-hypothesis-injection` in `lemma cartan_inv_of_isUnit` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L83 [advisory] `local-hypothesis-injection` in `lemma cartan_inv_of_isUnit` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L89 [advisory] `local-hypothesis-injection` in `lemma cartan_inv_of_isUnit` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L101 [advisory] `local-hypothesis-injection` in `lemma cartan_inv_of_isUnit` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L123 [advisory] `local-hypothesis-injection` in `lemma Jn_transpose` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L129 [advisory] `local-hypothesis-injection` in `lemma Jn_transpose` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

