# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:01.264203+00:00`
Root: `lean/InfoGeometry/Measure/Normalized.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **14**
- Hard: **0**
- Soft: **9**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Measure/Normalized.lean` | `advisory` | 23 | 0 | 9 | 5 | 14 |

## Findings by file

### `lean/InfoGeometry/Measure/Normalized.lean`
- module: `InfoGeometry.Measure.Normalized`
- status: `advisory`
- debt_score: `23`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L17 [advisory] `existential-packaging` in `def normalizedSlice` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L27 [soft] `simp-law-injection` in `simp-declaration probMeasureToUState_ne_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L33 [advisory] `existential-packaging` in `abbrev probMeasureToNonzero` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L37 [soft] `simp-law-injection` in `simp-declaration normalizedSlice_probMeasureToNonzero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L44 [advisory] `existential-packaging` in `def probMeasureToProjectiveState` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L49 [soft] `simp-law-injection` in `simp-declaration normalize_probMeasureToProjectiveState` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L61 [advisory] `existential-packaging` in `def pmfToProjectiveState` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L65 [soft] `simp-law-injection` in `simp-declaration normalize_pmfToProjectiveState` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L78 [soft] `simp-law-injection` in `simp-declaration probMeasureToPMF_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L83 [soft] `simp-law-injection` in `simp-declaration probMeasureToPMF_pmfToProbMeasure` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L90 [soft] `simp-law-injection` in `simp-declaration pmfToProbMeasure_probMeasureToPMF` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L101 [soft] `simp-law-injection` in `simp-declaration logPotential_pmf_eq_log_rnDeriv` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L109 [soft] `simp-law-injection` in `simp-declaration logPotential_pmf_self_ae` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

