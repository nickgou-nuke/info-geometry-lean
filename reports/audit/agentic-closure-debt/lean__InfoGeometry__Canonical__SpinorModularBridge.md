# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:00.217079+00:00`
Root: `lean/InfoGeometry/Canonical/SpinorModularBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **17**
- Hard: **0**
- Soft: **3**
- Advisory: **14**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SpinorModularBridge.lean` | `advisory` | 20 | 0 | 3 | 14 | 17 |

## Findings by file

### `lean/InfoGeometry/Canonical/SpinorModularBridge.lean`
- module: `InfoGeometry.Canonical.SpinorModularBridge`
- status: `advisory`
- debt_score: `20`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L38 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L40 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L69 [soft] `skeletal-proof` in `theorem horizon_is_scale_invariant` — proof appears to close via minimal tactic one-liner
  - L143 [advisory] `existential-packaging` in `theorem boundaryGenerator_ne_zero_of_exists_danglingZeroMode` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L154 [advisory] `existential-packaging` in `theorem boundaryScale_ne_zero_of_exists_danglingZeroMode` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L160 [advisory] `local-hypothesis-injection` in `theorem boundaryScale_ne_zero_of_exists_danglingZeroMode` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L165 [soft] `skeletal-proof` in `theorem boundary_active_on_nonzero_kernel_of_kernel_separation` — proof appears to close via minimal tactic one-liner
  - L186 [soft] `skeletal-proof` in `theorem kernel_separation_of_boundary_active_on_nonzero_kernel` — proof appears to close via minimal tactic one-liner
  - L202 [advisory] `local-hypothesis-injection` in `theorem kernel_separation_of_boundary_active_on_nonzero_kernel` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L241 [advisory] `existential-packaging` in `theorem exists_danglingZeroMode_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L263 [advisory] `local-hypothesis-injection` in `theorem exists_danglingZeroMode_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L277 [advisory] `existential-packaging` in `theorem exists_danglingZeroMode_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_identifiedTransportedPolarization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L295 [advisory] `local-hypothesis-injection` in `theorem exists_danglingZeroMode_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_identifiedTransportedPolarization` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L298 [advisory] `local-hypothesis-injection` in `theorem exists_danglingZeroMode_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_identifiedTransportedPolarization` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L477 [advisory] `existential-packaging` in `theorem exists_localizedBoundaryVortex_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L506 [advisory] `existential-packaging` in `theorem exists_localizedBoundaryVortex_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_identifiedTransportedPolarization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

