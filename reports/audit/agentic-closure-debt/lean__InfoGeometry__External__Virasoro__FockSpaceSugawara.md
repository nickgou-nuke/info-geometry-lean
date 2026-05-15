# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:31.597681+00:00`
Root: `lean/InfoGeometry/External/Virasoro/FockSpaceSugawara.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **6**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/External/Virasoro/FockSpaceSugawara.lean` | `advisory` | 13 | 0 | 6 | 1 | 7 |

## Findings by file

### `lean/InfoGeometry/External/Virasoro/FockSpaceSugawara.lean`
- module: `InfoGeometry.External.Virasoro.FockSpaceSugawara`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L155 [soft] `skeletal-proof` in `lemma sugawaraRepresentation_lgen_apply_vacuum` — proof appears to close via minimal tactic one-liner
  - L172 [soft] `skeletal-proof` in `lemma sugawaraRepresentation_lgen_nonneg_apply_vacuum` — proof appears to close via minimal tactic one-liner
  - L192 [soft] `skeletal-proof` in `lemma sugawaraRepresentation_lgen_pos_apply_vacuum` — proof appears to close via minimal tactic one-liner
  - L201 [soft] `simp-law-injection` in `simp-declaration sugawaraRepresentation_cgen_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L210 [soft] `simp-law-injection` in `simp-declaration sugawaraRepresentation_smul_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L224 [soft] `simp-law-injection` in `simp-declaration algebraMap_virasoro_smul_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

