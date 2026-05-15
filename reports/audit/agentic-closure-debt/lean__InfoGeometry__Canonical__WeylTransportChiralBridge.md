# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:13.526758+00:00`
Root: `lean/InfoGeometry/Canonical/WeylTransportChiralBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **4**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/WeylTransportChiralBridge.lean` | `advisory` | 14 | 0 | 4 | 6 | 10 |

## Findings by file

### `lean/InfoGeometry/Canonical/WeylTransportChiralBridge.lean`
- module: `InfoGeometry.Canonical.WeylTransportChiralBridge`
- status: `advisory`
- debt_score: `14`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L19 [soft] `law-field-locker` in `structure-field FlatCurvatureValueBridge.flat_to_zeroCurvatureIntegral` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L23 [soft] `law-field-locker` in `structure-field FlatCurvatureValueBridge.zeroCurvatureIntegral_to_target` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L89 [soft] `skeletal-proof` in `theorem holonomy_eq_projectorObstruction_nnnorm_of_flat` — proof appears to close via minimal tactic one-liner
  - L106 [advisory] `bridge-shaped-declaration` in `theorem holonomy_eq_chiralScale_of_flat_compat` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L124 [soft] `skeletal-proof` in `theorem holonomy_eq_chiralScale_of_flat` — proof appears to close via minimal tactic one-liner
  - L255 [advisory] `bridge-shaped-declaration` in `theorem finiteSum_holonomy_eq_chiralScale_of_flat_compat` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L311 [advisory] `local-hypothesis-injection` in `theorem holonomy_eq_zero_of_flat_of_unitRelativeVolume` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L334 [advisory] `local-hypothesis-injection` in `theorem holonomy_pos_of_flat_of_noncommute` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L336 [advisory] `local-hypothesis-injection` in `theorem holonomy_pos_of_flat_of_noncommute` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

