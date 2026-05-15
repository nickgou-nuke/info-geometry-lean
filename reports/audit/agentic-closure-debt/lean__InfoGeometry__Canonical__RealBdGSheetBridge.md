# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:47.804468+00:00`
Root: `lean/InfoGeometry/Canonical/RealBdGSheetBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **20**
- Hard: **0**
- Soft: **12**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RealBdGSheetBridge.lean` | `advisory` | 32 | 0 | 12 | 8 | 20 |

## Findings by file

### `lean/InfoGeometry/Canonical/RealBdGSheetBridge.lean`
- module: `InfoGeometry.Canonical.RealBdGSheetBridge`
- status: `advisory`
- debt_score: `32`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L14 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L16 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L52 [soft] `simp-law-injection` in `simp-declaration dualSheetChiralLift_apply_to_doubled` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L60 [soft] `simp-law-injection` in `simp-declaration plusBlockMap_dualSheetChiralLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L67 [soft] `simp-law-injection` in `simp-declaration minusBlockMap_dualSheetChiralLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L74 [soft] `simp-law-injection` in `simp-declaration plusToMinusBlockMap_dualSheetChiralLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L81 [soft] `simp-law-injection` in `simp-declaration minusToPlusBlockMap_dualSheetChiralLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L86 [soft] `simp-law-injection` in `simp-declaration KConjugate_liftedOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L94 [advisory] `local-hypothesis-injection` in `abbrev chiralImbalanceLift` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L104 [soft] `simp-law-injection` in `simp-declaration KLinearPart_liftedOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L112 [advisory] `local-hypothesis-injection` in `abbrev chiralImbalanceLift` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L123 [soft] `simp-law-injection` in `simp-declaration KAntilinearPart_liftedOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L131 [advisory] `local-hypothesis-injection` in `abbrev chiralImbalanceLift` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L141 [soft] `skeletal-proof` in `theorem commonModeLift_is_KLinear` — proof appears to close via minimal tactic one-liner
  - L148 [soft] `skeletal-proof` in `theorem chiralImbalanceLift_is_KAntilinear` — proof appears to close via minimal tactic one-liner
  - L155 [soft] `simp-law-injection` in `simp-declaration KAntilinearPart_liftedOperator_eq_zero_of_isGaugeBalanced` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L163 [advisory] `local-hypothesis-injection` in `theorem chiralImbalanceLift_is_KAntilinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L169 [soft] `simp-law-injection` in `simp-declaration KLinearPart_liftedOperator_eq_liftedOperator_of_isGaugeBalanced` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L178 [advisory] `local-hypothesis-injection` in `theorem chiralImbalanceLift_is_KAntilinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

