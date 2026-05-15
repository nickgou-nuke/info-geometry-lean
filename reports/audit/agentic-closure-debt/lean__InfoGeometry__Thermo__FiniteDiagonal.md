# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:46.518824+00:00`
Root: `lean/InfoGeometry/Thermo/FiniteDiagonal.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **7**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Thermo/FiniteDiagonal.lean` | `advisory` | 22 | 0 | 7 | 8 | 15 |

## Findings by file

### `lean/InfoGeometry/Thermo/FiniteDiagonal.lean`
- module: `InfoGeometry.Thermo.FiniteDiagonal`
- status: `advisory`
- debt_score: `22`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L105 [advisory] `existential-packaging` in `lemma gibbsWeight_eq_exp_logDensity` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L105 [soft] `skeletal-proof` in `lemma gibbsWeight_eq_exp_logDensity` — proof appears to close via minimal tactic one-liner
  - L109 [advisory] `local-hypothesis-injection` in `lemma gibbsWeight_eq_exp_logDensity` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L118 [soft] `simp-law-injection` in `simp-declaration modularShift_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L122 [advisory] `existential-packaging` in `lemma modularShift_zero` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L128 [advisory] `existential-packaging` in `lemma modularShift_add` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L128 [soft] `skeletal-proof` in `lemma modularShift_add` — proof appears to close via minimal tactic one-liner
  - L131 [advisory] `local-hypothesis-injection` in `lemma modularShift_add` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L136 [soft] `skeletal-proof` in `lemma modularShift_diag_fixed` — proof appears to close via minimal tactic one-liner
  - L139 [advisory] `existential-packaging` in `lemma gibbsState_one` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L165 [advisory] `local-hypothesis-injection` in `lemma gibbsWeight_transport` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L174 [soft] `skeletal-proof` in `lemma gibbs_detailedBalance_entry` — proof appears to close via minimal tactic one-liner
  - L188 [soft] `skeletal-proof` in `lemma gibbsDensity_diag_pos` — proof appears to close via minimal tactic one-liner
  - L193 [soft] `skeletal-proof` in `lemma logDensityOp_exp_entry` — proof appears to close via minimal tactic one-liner

