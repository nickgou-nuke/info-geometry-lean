# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:00.622745+00:00`
Root: `lean/InfoGeometry/Canonical/SplitCliffordHeadLift.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **21**
- Hard: **0**
- Soft: **16**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SplitCliffordHeadLift.lean` | `advisory` | 37 | 0 | 16 | 5 | 21 |

## Findings by file

### `lean/InfoGeometry/Canonical/SplitCliffordHeadLift.lean`
- module: `InfoGeometry.Canonical.SplitCliffordHeadLift`
- status: `advisory`
- debt_score: `37`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L53 [soft] `simp-law-injection` in `simp-declaration headJTensor_preimage` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L58 [soft] `simp-law-injection` in `simp-declaration headKTensor_preimage` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L63 [soft] `simp-law-injection` in `simp-declaration headJTensor_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L68 [soft] `simp-law-injection` in `simp-declaration headKTensor_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L73 [soft] `simp-law-injection` in `simp-declaration headJTensor_mul_headKTensor_add_swap` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L79 [advisory] `local-hypothesis-injection` in `def headNullPlusTensor` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L89 [soft] `simp-law-injection` in `simp-declaration headKTensor_mul_headJTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L96 [soft] `simp-law-injection` in `simp-declaration headEpsTensor_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L100 [advisory] `local-hypothesis-injection` in `def headNullPlusTensor` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L112 [soft] `simp-law-injection` in `simp-declaration headJTensor_mul_headEpsTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L120 [soft] `simp-law-injection` in `simp-declaration headEpsTensor_mul_headJTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L124 [advisory] `local-hypothesis-injection` in `def headNullPlusTensor` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L135 [soft] `simp-law-injection` in `simp-declaration headKTensor_mul_headEpsTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L139 [advisory] `local-hypothesis-injection` in `def headNullPlusTensor` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L150 [soft] `simp-law-injection` in `simp-declaration headEpsTensor_mul_headKTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L171 [soft] `simp-law-injection` in `simp-declaration headNullMinusTensor_eq_formula` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L204 [soft] `simp-law-injection` in `simp-declaration headNullPlusTensor_eq_formula` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L239 [soft] `simp-law-injection` in `simp-declaration headNullMinusTensor_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L244 [soft] `simp-law-injection` in `simp-declaration headNullPlusTensor_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L249 [soft] `simp-law-injection` in `simp-declaration headNullMinusTensor_mul_headNullPlusTensor_add_swap` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

