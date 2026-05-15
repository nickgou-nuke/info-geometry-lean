# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:32.704823+00:00`
Root: `lean/InfoGeometry/External/Virasoro/SectionSES.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **4**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/External/Virasoro/SectionSES.lean` | `advisory` | 14 | 0 | 4 | 6 | 10 |

## Findings by file

### `lean/InfoGeometry/External/Virasoro/SectionSES.lean`
- module: `InfoGeometry.External.Virasoro.SectionSES`
- status: `advisory`
- debt_score: `14`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L156 [advisory] `existential-packaging` in `def choose_section` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L166 [advisory] `existential-packaging` in `lemma choose_section_prop` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L189 [soft] `skeletal-proof` in `lemma correctorHom_smul` — proof appears to close via minimal tactic one-liner
  - L194 [advisory] `local-hypothesis-injection` in `lemma correctorHom_smul` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L244 [soft] `skeletal-proof` in `lemma ses_directSum_isInternal` — proof appears to close via minimal tactic one-liner
  - L259 [advisory] `local-hypothesis-injection` in `lemma ses_directSum_isInternal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L277 [advisory] `local-hypothesis-injection` in `lemma ses_directSum_isInternal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L325 [soft] `simp-law-injection` in `simp-declaration ses_basis_eq_of_left` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L330 [soft] `simp-law-injection` in `simp-declaration ses_basis_eq_of_right` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

