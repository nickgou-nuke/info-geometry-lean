# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:00.732189+00:00`
Root: `lean/InfoGeometry/Canonical/SplitCliffordHeadPhaseFlip.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **17**
- Hard: **0**
- Soft: **15**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SplitCliffordHeadPhaseFlip.lean` | `advisory` | 32 | 0 | 15 | 2 | 17 |

## Findings by file

### `lean/InfoGeometry/Canonical/SplitCliffordHeadPhaseFlip.lean`
- module: `InfoGeometry.Canonical.SplitCliffordHeadPhaseFlip`
- status: `advisory`
- debt_score: `32`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L60 [soft] `simp-law-injection` in `simp-declaration headKFlipCarrier_headPair` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L67 [soft] `simp-law-injection` in `simp-declaration headKFlipCarrier_tailLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L73 [soft] `simp-law-injection` in `simp-declaration headKFlipCarrier_headNullMinus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L79 [soft] `simp-law-injection` in `simp-declaration headKFlipCarrier_headNullPlus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L85 [soft] `simp-law-injection` in `simp-declaration headKFlipIsometry_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L90 [soft] `simp-law-injection` in `simp-declaration headKFlipAlg_apply_` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L100 [soft] `simp-law-injection` in `simp-declaration headKFlipAlg_headJ` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L107 [soft] `simp-law-injection` in `simp-declaration headKFlipAlg_headK` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L120 [advisory] `local-hypothesis-injection` in `def headKFlipTensor` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L126 [soft] `simp-law-injection` in `simp-declaration headKFlipAlg_headNullMinus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L132 [soft] `simp-law-injection` in `simp-declaration headKFlipAlg_headNullPlus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L138 [soft] `simp-law-injection` in `simp-declaration headKFlipTensor_apply_headJTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L147 [soft] `simp-law-injection` in `simp-declaration headKFlipTensor_apply_headKTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L156 [soft] `simp-law-injection` in `simp-declaration headKFlipTensor_apply_headEpsTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L162 [soft] `simp-law-injection` in `simp-declaration headKFlipTensor_apply_headNullMinusTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L171 [soft] `simp-law-injection` in `simp-declaration headKFlipTensor_apply_headNullPlusTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

