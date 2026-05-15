# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:59.550764+00:00`
Root: `lean/InfoGeometry/Canonical/SpectroscopicGauge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **14**
- Hard: **0**
- Soft: **11**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SpectroscopicGauge.lean` | `advisory` | 25 | 0 | 11 | 3 | 14 |

## Findings by file

### `lean/InfoGeometry/Canonical/SpectroscopicGauge.lean`
- module: `InfoGeometry.Canonical.SpectroscopicGauge`
- status: `advisory`
- debt_score: `25`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L39 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L41 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L56 [soft] `law-field-locker` in `structure-field SpectroscopicGaugeData.kmsCompat` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L57 [soft] `law-field-locker` in `structure-field SpectroscopicGaugeData.datum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L58 [soft] `law-field-locker` in `structure-field SpectroscopicGaugeData.probe_eq_referenceState` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [soft] `law-field-locker` in `structure-field SpectroscopicGaugeData.isProjector` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [soft] `simp-law-injection` in `simp-declaration referenceState_eq_probe` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L76 [soft] `skeletal-proof` in `theorem referenceState_eq_probe` — proof appears to close via minimal tactic one-liner
  - L86 [soft] `skeletal-proof` in `theorem referenceState_owned_unruh_kms_identity` — proof appears to close via minimal tactic one-liner
  - L120 [soft] `simp-law-injection` in `simp-declaration gaugeObstruction_eq_zero_of_commute` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L132 [soft] `skeletal-proof` in `theorem measuredCrossPacket_swap` — proof appears to close via minimal tactic one-liner
  - L158 [soft] `skeletal-proof` in `theorem relativity_of_measurements_of_same_datum_and_probe` — proof appears to close via minimal tactic one-liner
  - L179 [soft] `simp-law-injection` in `simp-declaration spectralPacketShift_eq_zero_of_same_datum_and_probe` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

