# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:17.046679+00:00`
Root: `lean/InfoGeometry/Clifford/ClNNBilinear.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **22**
- Hard: **0**
- Soft: **17**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Clifford/ClNNBilinear.lean` | `advisory` | 39 | 0 | 17 | 5 | 22 |

## Findings by file

### `lean/InfoGeometry/Clifford/ClNNBilinear.lean`
- module: `InfoGeometry.Clifford.ClNNBilinear`
- status: `advisory`
- debt_score: `39`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L86 [soft] `simp-law-injection` in `simp-declaration Bsplit_zero_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L91 [soft] `simp-law-injection` in `simp-declaration Bsplit_succ_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L101 [soft] `simp-law-injection` in `simp-declaration hyperbolicQuadratic_zero_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L106 [soft] `simp-law-injection` in `simp-declaration hyperbolicQuadratic_succ_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L112 [soft] `simp-law-injection` in `simp-declaration hyperbolicBilinear_succ_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L154 [soft] `skeletal-proof` in `theorem polar_Qsplit_eq_two_Bsplit` — proof appears to close via minimal tactic one-liner
  - L159 [advisory] `local-hypothesis-injection` in `theorem polar_Qsplit_eq_two_Bsplit` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L160 [advisory] `local-hypothesis-injection` in `theorem polar_Qsplit_eq_two_Bsplit` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L167 [advisory] `local-hypothesis-injection` in `theorem polar_Qsplit_eq_two_Bsplit` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L175 [advisory] `local-hypothesis-injection` in `theorem polar_Qsplit_eq_two_Bsplit` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L182 [soft] `skeletal-proof` in `theorem hyperbolic_polar_eq_two_bilinear` — proof appears to close via minimal tactic one-liner
  - L187 [soft] `simp-law-injection` in `simp-declaration Bsplit_headPair_tailLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L192 [soft] `simp-law-injection` in `simp-declaration Bsplit_tailLift_headPair` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L198 [soft] `simp-law-injection` in `simp-declaration Bsplit_headPair_headPair` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L203 [soft] `simp-law-injection` in `simp-declaration Bsplit_tailLift_tailLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L233 [soft] `skeletal-proof` in `theorem clifford_head_tail_anticommute` — proof appears to close via minimal tactic one-liner
  - L242 [soft] `simp-law-injection` in `simp-declaration hyperbolic_headNullMinus_isotropic` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L247 [soft] `simp-law-injection` in `simp-declaration hyperbolic_headNullPlus_isotropic` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L252 [soft] `simp-law-injection` in `simp-declaration hyperbolic_headNullMinus_headNullPlus_pairing` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L260 [soft] `simp-law-injection` in `simp-declaration hyperbolic_headNullPlus_headNullMinus_pairing` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L277 [soft] `skeletal-proof` in `theorem gammaHeadNullMinus_mul_gammaHeadNullPlus_add_swap_eq_hyperbolic_pairing` — proof appears to close via minimal tactic one-liner

