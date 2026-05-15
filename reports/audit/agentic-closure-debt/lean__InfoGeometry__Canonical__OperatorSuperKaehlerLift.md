# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:37.249438+00:00`
Root: `lean/InfoGeometry/Canonical/OperatorSuperKaehlerLift.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **8**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/OperatorSuperKaehlerLift.lean` | `advisory` | 20 | 0 | 8 | 4 | 12 |

## Findings by file

### `lean/InfoGeometry/Canonical/OperatorSuperKaehlerLift.lean`
- module: `InfoGeometry.Canonical.OperatorSuperKaehlerLift`
- status: `advisory`
- debt_score: `20`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L40 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L42 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L43 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L60 [soft] `law-field-locker` in `structure-field OperatorSuperKaehlerMassieuPacket.hestenes` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L61 [soft] `law-field-locker` in `structure-field OperatorSuperKaehlerMassieuPacket.potential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L88 [soft] `simp-law-injection` in `simp-declaration massieuPotential_eq_operatorMassieuPotential` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L90 [soft] `skeletal-proof` in `theorem massieuPotential_eq_operatorMassieuPotential` — proof appears to close via minimal tactic one-liner
  - L148 [soft] `simp-law-injection` in `simp-declaration phaseResponse_eq_metric_comp_channelPhaseAxis` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L150 [soft] `skeletal-proof` in `theorem phaseResponse_eq_metric_comp_channelPhaseAxis` — proof appears to close via minimal tactic one-liner
  - L157 [soft] `simp-law-injection` in `simp-declaration phaseResponse_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L159 [soft] `skeletal-proof` in `theorem phaseResponse_apply` — proof appears to close via minimal tactic one-liner

