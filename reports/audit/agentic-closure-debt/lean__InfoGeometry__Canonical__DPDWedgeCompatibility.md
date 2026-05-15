# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:58.743872+00:00`
Root: `lean/InfoGeometry/Canonical/DPDWedgeCompatibility.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **17**
- Hard: **0**
- Soft: **12**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DPDWedgeCompatibility.lean` | `advisory` | 29 | 0 | 12 | 5 | 17 |

## Findings by file

### `lean/InfoGeometry/Canonical/DPDWedgeCompatibility.lean`
- module: `InfoGeometry.Canonical.DPDWedgeCompatibility`
- status: `advisory`
- debt_score: `29`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L20 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L22 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L40 [soft] `law-field-locker` in `structure-field IsCompatibleDPDWedge.hPlus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L41 [soft] `law-field-locker` in `structure-field IsCompatibleDPDWedge.hMinus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L42 [soft] `law-field-locker` in `structure-field IsCompatibleDPDWedge.hZero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `skeletal-proof` in `theorem kernelConventionLock_pzero_eq_spectralComplementaryProjector` — proof appears to close via minimal tactic one-liner
  - L65 [soft] `skeletal-proof` in `theorem activeProjector_eq_one_sub_spectralComplementaryProjector` — proof appears to close via minimal tactic one-liner
  - L83 [soft] `skeletal-proof` in `theorem wedgeSign_sq_eq_spectralProjector` — proof appears to close via minimal tactic one-liner
  - L102 [soft] `skeletal-proof` in `theorem wedgeSign_mul_spectralComplementaryProjector_eq_zero` — proof appears to close via minimal tactic one-liner
  - L119 [soft] `skeletal-proof` in `theorem spectralComplementaryProjector_mul_wedgeSign_eq_zero` — proof appears to close via minimal tactic one-liner
  - L147 [soft] `skeletal-proof` in `theorem two_smul_dilationGap_eq_wedgeSign` — proof appears to close via minimal tactic one-liner
  - L163 [soft] `skeletal-proof` in `theorem dilationGap_eq_half_wedgeSign` — proof appears to close via minimal tactic one-liner
  - L166 [advisory] `local-hypothesis-injection` in `theorem dilationGap_eq_half_wedgeSign` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L274 [soft] `skeletal-proof` in `theorem relativeModular_offDiagonal_blocks_zero_of_commutes_spectralProjector` — proof appears to close via minimal tactic one-liner
  - L308 [soft] `skeletal-proof` in `theorem relativeModular_scaleShapeSplit` — proof appears to close via minimal tactic one-liner
  - L319 [advisory] `local-hypothesis-injection` in `theorem relativeModular_scaleShapeSplit` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

