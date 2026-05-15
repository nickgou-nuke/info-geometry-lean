# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:06.538113+00:00`
Root: `lean/InfoGeometry/Canonical/EPDefectAlgebra.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **6**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/EPDefectAlgebra.lean` | `advisory` | 16 | 0 | 6 | 4 | 10 |

## Findings by file

### `lean/InfoGeometry/Canonical/EPDefectAlgebra.lean`
- module: `InfoGeometry.Canonical.EPDefectAlgebra`
- status: `advisory`
- debt_score: `16`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L24 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L46 [soft] `simp-law-injection` in `simp-declaration mpLeftProj_idempotent` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L50 [soft] `simp-law-injection` in `simp-declaration mpRightProj_idempotent` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L54 [soft] `simp-law-injection` in `simp-declaration drazinCoreProj_idempotent` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L58 [soft] `simp-law-injection` in `simp-declaration mpInverseCommutator_eq_mpChiralGap` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L68 [soft] `simp-law-injection` in `simp-declaration dilationGap_eq_half_smul_mpChiralGap` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L72 [soft] `simp-law-injection` in `simp-declaration dilationGap_eq_half_smul_mpInverseCommutator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L82 [advisory] `local-hypothesis-injection` in `def mpInverseCommutator` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L85 [advisory] `local-hypothesis-injection` in `def mpInverseCommutator` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

