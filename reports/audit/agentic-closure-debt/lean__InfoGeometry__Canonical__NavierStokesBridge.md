# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:32.714996+00:00`
Root: `lean/InfoGeometry/Canonical/NavierStokesBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **28**
- Hard: **0**
- Soft: **18**
- Advisory: **10**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/NavierStokesBridge.lean` | `advisory` | 46 | 0 | 18 | 10 | 28 |

## Findings by file

### `lean/InfoGeometry/Canonical/NavierStokesBridge.lean`
- module: `InfoGeometry.Canonical.NavierStokesBridge`
- status: `advisory`
- debt_score: `46`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L75 [soft] `skeletal-proof` in `theorem adjoint_vorticity_eq_neg` — proof appears to close via minimal tactic one-liner
  - L93 [soft] `skeletal-proof` in `theorem adjoint_strainRate_eq_self` — proof appears to close via minimal tactic one-liner
  - L154 [soft] `simp-law-injection` in `simp-declaration anomalyFluidStateWithDensity_u` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L161 [soft] `simp-law-injection` in `simp-declaration anomalyFluidStateWithDensity_rho` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L177 [soft] `skeletal-proof` in `theorem modular_circulation_response` — proof appears to close via minimal tactic one-liner
  - L196 [soft] `skeletal-proof` in `lemma vorticity_eq_self_of_skew` — proof appears to close via minimal tactic one-liner
  - L263 [soft] `skeletal-proof` in `theorem anomaly_as_fluid_state` — proof appears to close via minimal tactic one-liner
  - L299 [soft] `skeletal-proof` in `theorem anomalyMomentumResidual_eq_zero_of_regularization` — proof appears to close via minimal tactic one-liner
  - L321 [advisory] `existential-packaging` in `theorem anomalyMomentumResidual_eq_zero_of_regularization_exists` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L354 [advisory] `existential-packaging` in `theorem anomalyFluidState_momentumResidual_eq_zero_of_regularization_exists` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L367 [advisory] `existential-packaging` in `theorem anomalySkew_of_regularization_of_finiteDimensional` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L397 [advisory] `existential-packaging` in `theorem anomalyMomentumResidual_eq_zero_of_regularization_of_finiteDimensional` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L416 [advisory] `existential-packaging` in `theorem anomalyFluidState_momentumResidual_eq_zero_of_regularization_of_finiteDimensional` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L435 [advisory] `existential-packaging` in `theorem anomalyMomentumResidual_eq_zero_of_regularization_global_drazin` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L459 [advisory] `existential-packaging` in `theorem anomalyFluidState_momentumResidual_eq_zero_of_regularization_global_drazin` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L483 [soft] `skeletal-proof` in `theorem anomalySkew_of_regularization_auto` — proof appears to close via minimal tactic one-liner
  - L509 [soft] `skeletal-proof` in `theorem anomalySkew_of_regularization_canonical_drazin` — proof appears to close via minimal tactic one-liner
  - L656 [soft] `skeletal-proof` in `theorem hasDerivAt_modularVelocity_zero` — proof appears to close via minimal tactic one-liner
  - L668 [advisory] `local-hypothesis-injection` in `theorem hasDerivAt_modularVelocity_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L769 [advisory] `local-hypothesis-injection` in `lemma madelungDensity_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L802 [soft] `simp-law-injection` in `simp-declaration madelungFluidState_velocity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L823 [soft] `law-field-locker` in `structure-field SmoothedMadelungFluidState.smoothed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L824 [soft] `law-field-locker` in `structure-field SmoothedMadelungFluidState.velocity_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L863 [soft] `simp-law-injection` in `simp-declaration madelungFluidState_zero_velocity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L870 [soft] `simp-law-injection` in `simp-declaration smoothedMadelungFluidState_zero_velocity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L934 [soft] `skeletal-proof` in `theorem twinWaveHelicity_def` — proof appears to close via minimal tactic one-liner
  - L990 [soft] `skeletal-proof` in `theorem chiralFlux_EinsteinAnomaly_def` — proof appears to close via minimal tactic one-liner

