# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:01.935353+00:00`
Root: `lean/InfoGeometry/Canonical/StandardFormOmegaVolumeBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **16**
- Hard: **0**
- Soft: **12**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/StandardFormOmegaVolumeBridge.lean` | `advisory` | 28 | 0 | 12 | 4 | 16 |

## Findings by file

### `lean/InfoGeometry/Canonical/StandardFormOmegaVolumeBridge.lean`
- module: `InfoGeometry.Canonical.StandardFormOmegaVolumeBridge`
- status: `advisory`
- debt_score: `28`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L41 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L43 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L69 [soft] `law-field-locker` in `structure-field NaturalConeVolumeBridge.volumeState` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [soft] `law-field-locker` in `structure-field NaturalConeVolumeBridge.volumeState_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L75 [soft] `law-field-locker` in `structure-field NaturalConeVolumeBridge.volumeState_word_sum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L80 [soft] `law-field-locker` in `structure-field NaturalConeVolumeBridge.volumeState_eq_omega_kreinExpectation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L85 [soft] `law-field-locker` in `structure-field NaturalConeVolumeBridge.cylinderProjector_partition_unity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L94 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L94 [soft] `section-law-variable` in `variable B` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L136 [soft] `skeletal-proof` in `theorem wignerJonesAtom_partition_unity` — proof appears to close via minimal tactic one-liner
  - L146 [soft] `skeletal-proof` in `theorem total_expectation_is_unity` — proof appears to close via minimal tactic one-liner
  - L163 [soft] `skeletal-proof` in `theorem total_localizedExpectation_is_unity` — proof appears to close via minimal tactic one-liner
  - L189 [soft] `skeletal-proof` in `theorem modularVolumePotential_eq_neg_log_atomExpectation` — proof appears to close via minimal tactic one-liner
  - L196 [soft] `skeletal-proof` in `theorem modularVolumeIncrement_eq_neg_log_ratio` — proof appears to close via minimal tactic one-liner
  - L209 [soft] `skeletal-proof` in `theorem modularVolumeIncrement_common_pos_smul` — proof appears to close via minimal tactic one-liner

