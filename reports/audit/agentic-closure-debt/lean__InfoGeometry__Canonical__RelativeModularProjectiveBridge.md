# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:51.495259+00:00`
Root: `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **5**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean` | `advisory` | 13 | 0 | 5 | 3 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean`
- module: `InfoGeometry.Canonical.RelativeModularProjectiveBridge`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L62 [soft] `simp-law-injection` in `simp-declaration RestrictedRelativeModularData.local_projectiveLogGenerator_eq_local_modularPotential` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L111 [soft] `simp-law-injection` in `simp-declaration RestrictedRelativeModularData.local_projectiveLogGenerator_eq_pullback_ambient_add_shift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L117 [advisory] `existential-packaging` in `theorem RestrictedRelativeModularData.local_projectiveLogGenerator_eq_pullback_ambient_add_shift` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L138 [soft] `simp-law-injection` in `simp-declaration RestrictedRelativeModularData.local_modularPotential_eq_projectiveCountHamiltonianProfile_of_countRays` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L161 [soft] `simp-law-injection` in `simp-declaration RestrictedRelativeModularData.projectiveCountHamiltonianProfile_eq_pullback_ambient_add_shift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L167 [advisory] `existential-packaging` in `theorem RestrictedRelativeModularData.projectiveCountHamiltonianProfile_eq_pullback_ambient_add_shift` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L196 [soft] `simp-law-injection` in `simp-declaration RestrictedRelativeModularData.local_projectiveLogGenerator_eq_projectiveCountHamiltonianProfile_of_countRays` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

