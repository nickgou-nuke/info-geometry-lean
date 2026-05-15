# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:34.060222+00:00`
Root: `lean/InfoGeometry/Canonical/ObserverDefect.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **19**
- Hard: **0**
- Soft: **5**
- Advisory: **14**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ObserverDefect.lean` | `advisory` | 24 | 0 | 5 | 14 | 19 |

## Findings by file

### `lean/InfoGeometry/Canonical/ObserverDefect.lean`
- module: `InfoGeometry.Canonical.ObserverDefect`
- status: `advisory`
- debt_score: `24`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L17 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L19 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L35 [soft] `law-field-locker` in `structure-field ObserverL5.isOrientationFixing` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [soft] `simp-law-injection` in `simp-declaration localSlice_eq_spectralProjector_add_observerProjectorDeviation` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L150 [soft] `skeletal-proof` in `theorem projectorCompression_commutator_spectralProjector_dilationGap_eq_zero` — proof appears to close via minimal tactic one-liner
  - L165 [advisory] `local-hypothesis-injection` in `theorem projectorCompression_commutator_spectralProjector_dilationGap_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L167 [advisory] `local-hypothesis-injection` in `theorem projectorCompression_commutator_spectralProjector_dilationGap_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L190 [advisory] `local-hypothesis-injection` in `theorem observerDefectResidual_eq_projectorCompression_commutator_deviation` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L331 [advisory] `local-hypothesis-injection` in `theorem observerDefectResidual_norm_le_ZD_of_compressedDeviation_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L358 [advisory] `local-hypothesis-injection` in `theorem observerDefectResidual_eq_zero_of_deviationControlledByZD_of_ZD_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L361 [soft] `skeletal-proof` in `theorem two_smul_observerDefectResidual_eq_projectorCompression_commutator_localSlice_sigma_add_commutator_localSlice_geometricMismatch` — proof appears to close via minimal tactic one-liner
  - L435 [advisory] `local-hypothesis-injection` in `theorem observerDefectResidual_eq_zero_of_deviation_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L437 [advisory] `local-hypothesis-injection` in `theorem observerDefectResidual_eq_zero_of_deviation_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L463 [advisory] `local-hypothesis-injection` in `theorem observerDefectResidual_norm_le_ZD_of_deviation_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L482 [soft] `skeletal-proof` in `theorem observerDefectResidual_isDefectSupported` — proof appears to close via minimal tactic one-liner
  - L529 [advisory] `local-hypothesis-injection` in `theorem observerDefectResidual_commutes_complementaryProjector` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L556 [advisory] `local-hypothesis-injection` in `theorem observerDefectResidual_norm_le_ZD_of_aligned` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L614 [advisory] `local-hypothesis-injection` in `theorem observerDefectResidual_norm_le_ZD_of_strain_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

