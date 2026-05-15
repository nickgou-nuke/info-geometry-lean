# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:25.784896+00:00`
Root: `lean/InfoGeometry/Cramer.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **0**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Cramer.lean` | `advisory` | 8 | 0 | 0 | 8 | 8 |

## Findings by file

### `lean/InfoGeometry/Cramer.lean`
- module: `InfoGeometry.Cramer`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L8 [advisory] `existential-packaging` in `def cramerRateOn` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L16 [advisory] `existential-packaging` in `lemma le_cramerRateOn` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L26 [advisory] `existential-packaging` in `lemma fenchelYoung_on_cramerRateOn` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L36 [advisory] `existential-packaging` in `lemma exists_mem_eq_cramerRateOn` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L47 [advisory] `existential-packaging` in `lemma exists_argmax_cramerRateOn` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L57 [advisory] `local-hypothesis-injection` in `lemma exists_argmax_cramerRateOn` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L59 [advisory] `existential-packaging` in `lemma cramerRateOn_eq_of_mem_and_max` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

