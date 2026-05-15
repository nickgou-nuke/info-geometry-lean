# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:04.175188+00:00`
Root: `lean/InfoGeometry/Canonical/SuperchargeModularHamiltonianBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **8**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SuperchargeModularHamiltonianBridge.lean` | `advisory` | 19 | 0 | 8 | 3 | 11 |

## Findings by file

### `lean/InfoGeometry/Canonical/SuperchargeModularHamiltonianBridge.lean`
- module: `InfoGeometry.Canonical.SuperchargeModularHamiltonianBridge`
- status: `advisory`
- debt_score: `19`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L14 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L38 [soft] `law-field-locker` in `structure-field SuperchargeModularHamiltonianBridge.modularEnergyUnit_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L42 [soft] `law-field-locker` in `structure-field SuperchargeModularHamiltonianBridge.Ksur_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L53 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L53 [soft] `section-law-variable` in `variable H` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L66 [soft] `skeletal-proof` in `theorem spectralProjector_mul_Ksur` — proof appears to close via minimal tactic one-liner
  - L87 [soft] `skeletal-proof` in `theorem Ksur_mul_spectralProjector` — proof appears to close via minimal tactic one-liner
  - L108 [soft] `skeletal-proof` in `theorem spectralComplementaryProjector_mul_Ksur_eq_zero` — proof appears to close via minimal tactic one-liner
  - L128 [soft] `skeletal-proof` in `theorem Ksur_mul_spectralComplementaryProjector_eq_zero` — proof appears to close via minimal tactic one-liner
  - L148 [soft] `skeletal-proof` in `theorem Ksur_commutes_GammaS` — proof appears to close via minimal tactic one-liner

