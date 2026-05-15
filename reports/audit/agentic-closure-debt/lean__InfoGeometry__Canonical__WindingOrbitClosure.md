# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:13.931048+00:00`
Root: `lean/InfoGeometry/Canonical/WindingOrbitClosure.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **25**
- Hard: **0**
- Soft: **10**
- Advisory: **15**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/WindingOrbitClosure.lean` | `advisory` | 35 | 0 | 10 | 15 | 25 |

## Findings by file

### `lean/InfoGeometry/Canonical/WindingOrbitClosure.lean`
- module: `InfoGeometry.Canonical.WindingOrbitClosure`
- status: `advisory`
- debt_score: `35`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L38 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L94 [advisory] `local-hypothesis-injection` in `theorem multiBranchedGenerator_shift` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L97 [soft] `skeletal-proof` in `theorem modular_rotation_identity` — proof appears to close via minimal tactic one-liner
  - L105 [advisory] `local-hypothesis-injection` in `theorem modular_rotation_identity` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L111 [soft] `skeletal-proof` in `theorem winding_orbit_periodicity` — proof appears to close via minimal tactic one-liner
  - L122 [advisory] `local-hypothesis-injection` in `theorem winding_orbit_periodicity` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L123 [advisory] `local-hypothesis-injection` in `theorem winding_orbit_periodicity` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L128 [advisory] `local-hypothesis-injection` in `theorem winding_orbit_periodicity` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L129 [advisory] `local-hypothesis-injection` in `theorem winding_orbit_periodicity` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L132 [advisory] `local-hypothesis-injection` in `theorem winding_orbit_periodicity` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L166 [soft] `skeletal-proof` in `theorem modularTransportGenerator_commutes_clockAxis_of_forcingSeed` — proof appears to close via minimal tactic one-liner
  - L182 [advisory] `local-hypothesis-injection` in `theorem modularTransportGenerator_commutes_clockAxis_of_forcingSeed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L259 [soft] `law-field-locker` in `structure-field LocalClockGaugeSymmetryCertificate.branch_readout_faithful` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L298 [soft] `skeletal-proof` in `theorem winding_orbit_periodicity_modularGeneratorGaugePart` — proof appears to close via minimal tactic one-liner
  - L319 [advisory] `local-hypothesis-injection` in `theorem winding_orbit_periodicity_modularGeneratorGaugePart` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L345 [soft] `skeletal-proof` in `theorem modularTransportGenerator_commutes_clockAxis_of_detailedEquilibrium` — proof appears to close via minimal tactic one-liner
  - L362 [advisory] `local-hypothesis-injection` in `theorem modularTransportGenerator_commutes_clockAxis_of_detailedEquilibrium` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L523 [advisory] `local-hypothesis-injection` in `theorem modularTransportGenerator_commutator_clockAxis_eq_zero_of_cartanDualGrade` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L565 [soft] `skeletal-proof` in `theorem isNoncommutingScaleLane_iff_not_clockEquilibrium` — proof appears to close via minimal tactic one-liner
  - L660 [soft] `skeletal-proof` in `theorem nonEquilibriumClockDefect_eq_two_smul_scalePart_comp_clockAxis` — proof appears to close via minimal tactic one-liner
  - L686 [soft] `skeletal-proof` in `theorem right_comp_clockAxis_eq_zero_iff` — proof appears to close via minimal tactic one-liner
  - L701 [advisory] `local-hypothesis-injection` in `theorem right_comp_clockAxis_eq_zero_iff` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L704 [advisory] `local-hypothesis-injection` in `theorem right_comp_clockAxis_eq_zero_iff` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L737 [soft] `skeletal-proof` in `theorem modularTransportGenerator_clockAxis_commutator_eq_cartanScaleSource` — proof appears to close via minimal tactic one-liner

