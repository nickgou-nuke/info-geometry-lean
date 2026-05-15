# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:49.980568+00:00`
Root: `lean/InfoGeometry/Twistor/LightconeBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **2**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Twistor/LightconeBridge.lean` | `advisory` | 7 | 0 | 2 | 3 | 5 |

## Findings by file

### `lean/InfoGeometry/Twistor/LightconeBridge.lean`
- module: `InfoGeometry.Twistor.LightconeBridge`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L33 [soft] `simp-law-injection` in `simp-declaration twistorLift_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L35 [soft] `skeletal-proof` in `theorem twistorLift_apply` — proof appears to close via minimal tactic one-liner
  - L45 [advisory] `existential-packaging` in `theorem coordinates_emerge_as_adjoint` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L66 [advisory] `local-hypothesis-injection` in `theorem twistor_incidence_variety` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

