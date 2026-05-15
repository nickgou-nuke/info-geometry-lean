# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:47.823776+00:00`
Root: `lean/InfoGeometry/Thermo/ThermodynamicIdentities.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **1**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Thermo/ThermodynamicIdentities.lean` | `advisory` | 6 | 0 | 1 | 4 | 5 |

## Findings by file

### `lean/InfoGeometry/Thermo/ThermodynamicIdentities.lean`
- module: `InfoGeometry.Thermo.ThermodynamicIdentities`
- status: `advisory`
- debt_score: `6`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [advisory] `existential-packaging` in `def freeEnergy` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L50 [advisory] `existential-packaging` in `lemma entropy_eq_beta_internal_plus_massieu` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L54 [advisory] `local-hypothesis-injection` in `lemma entropy_eq_beta_internal_plus_massieu` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L109 [soft] `skeletal-proof` in `lemma beta_mul_freeEnergy` — proof appears to close via minimal tactic one-liner

