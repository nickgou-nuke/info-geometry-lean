# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:42.944018+00:00`
Root: `lean/InfoGeometry/Canonical/PolarizedMadelungBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **16**
- Hard: **0**
- Soft: **9**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/PolarizedMadelungBridge.lean` | `advisory` | 25 | 0 | 9 | 7 | 16 |

## Findings by file

### `lean/InfoGeometry/Canonical/PolarizedMadelungBridge.lean`
- module: `InfoGeometry.Canonical.PolarizedMadelungBridge`
- status: `advisory`
- debt_score: `25`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L34 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L49 [soft] `law-field-locker` in `structure-field PolarizedDoubledAmplitude.h_norm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [soft] `skeletal-proof` in `theorem sheet_decomposition` — proof appears to close via minimal tactic one-liner
  - L93 [soft] `simp-law-injection` in `simp-declaration phaseOrbit_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L123 [soft] `skeletal-proof` in `theorem modular_j_phaseOrbit_eq_reverse_complex_i` — proof appears to close via minimal tactic one-liner
  - L145 [soft] `simp-law-injection` in `simp-declaration norm_sq_plusPoint` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L152 [soft] `simp-law-injection` in `simp-declaration norm_sq_minusPoint` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L219 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L221 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L253 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L255 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L264 [soft] `law-field-locker` in `structure-field StateGeneratorField.generator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L308 [soft] `skeletal-proof` in `theorem statePhaseReadout_eq_metric_comp_complex_i` — proof appears to close via minimal tactic one-liner
  - L317 [soft] `skeletal-proof` in `theorem stateInducedDerivation_eq_gauge_add_source` — proof appears to close via minimal tactic one-liner

