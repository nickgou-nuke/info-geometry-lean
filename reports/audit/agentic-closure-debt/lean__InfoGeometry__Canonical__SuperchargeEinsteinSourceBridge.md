# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:03.698646+00:00`
Root: `lean/InfoGeometry/Canonical/SuperchargeEinsteinSourceBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **19**
- Hard: **0**
- Soft: **7**
- Advisory: **12**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SuperchargeEinsteinSourceBridge.lean` | `advisory` | 26 | 0 | 7 | 12 | 19 |

## Findings by file

### `lean/InfoGeometry/Canonical/SuperchargeEinsteinSourceBridge.lean`
- module: `InfoGeometry.Canonical.SuperchargeEinsteinSourceBridge`
- status: `advisory`
- debt_score: `26`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L42 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L60 [soft] `law-field-locker` in `structure-field SuperchargeProjectorCompatibility.spectralProj_eq_superchargeProj` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [soft] `law-field-locker` in `structure-field SuperchargeProjectorCompatibility.metricProj_eq_transportedProj` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L64 [soft] `law-field-locker` in `structure-field SuperchargeProjectorCompatibility.mismatch_forces_projector_noncommute` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L75 [advisory] `bridge-shaped-declaration` in `theorem projectorObstruction_ne_zero_of_compat_of_mismatch` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L100 [advisory] `bridge-shaped-declaration` in `theorem chiralScale_ne_zero_of_compat_of_mismatch` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L123 [advisory] `bridge-shaped-declaration` in `theorem chiralScale_ne_zero_and_einsteinEquation_of_compat_of_mismatch` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L158 [advisory] `bridge-shaped-declaration` in `theorem projectorObstruction_ne_zero_of_operatorialCentralCharge_ne_zero_of_compat` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L189 [advisory] `bridge-shaped-declaration` in `theorem projectorObstruction_ne_zero_of_quasilatticeAnalyticalIndex_ne_zero_of_compat` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L216 [advisory] `bridge-shaped-declaration` in `theorem chiralScale_ne_zero_and_einsteinEquation_of_operatorialCentralCharge_ne_zero_of_compat` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L255 [advisory] `bridge-shaped-declaration` in `theorem chiralScale_ne_zero_and_einsteinEquation_of_quasilatticeAnalyticalIndex_ne_zero_of_compat` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L372 [soft] `skeletal-proof` in `theorem mismatch_forces_projector_noncommute_of_boundaryScale_ne_zero` — proof appears to close via minimal tactic one-liner
  - L393 [advisory] `local-hypothesis-injection` in `theorem mismatch_forces_projector_noncommute_of_boundaryScale_ne_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L395 [advisory] `local-hypothesis-injection` in `theorem mismatch_forces_projector_noncommute_of_boundaryScale_ne_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L472 [advisory] `local-hypothesis-injection` in `theorem mismatch_forces_boundary_projector_noncommute_of_identifiedTransportedPolarization` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L746 [soft] `law-field-locker` in `structure-field SuperchargeBoundaryCarrierCompatibility.spectralProj_eq_superchargeProj` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L748 [soft] `law-field-locker` in `structure-field SuperchargeBoundaryCarrierCompatibility.metricProj_eq_transportedProj` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L750 [soft] `law-field-locker` in `structure-field SuperchargeBoundaryCarrierCompatibility.mismatch_forces_projector_noncommute` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

