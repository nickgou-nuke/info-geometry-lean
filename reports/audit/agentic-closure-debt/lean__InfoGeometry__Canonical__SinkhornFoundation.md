# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:55.930515+00:00`
Root: `lean/InfoGeometry/Canonical/SinkhornFoundation.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **30**
- Hard: **0**
- Soft: **18**
- Advisory: **12**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SinkhornFoundation.lean` | `advisory` | 48 | 0 | 18 | 12 | 30 |

## Findings by file

### `lean/InfoGeometry/Canonical/SinkhornFoundation.lean`
- module: `InfoGeometry.Canonical.SinkhornFoundation`
- status: `advisory`
- debt_score: `48`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L17 [advisory] `existential-packaging` in `def routerParams` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L26 [soft] `simp-law-injection` in `simp-declaration gc_partition_eq_routerPartition` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L30 [soft] `simp-law-injection` in `simp-declaration gc_gibbsWeight_eq_normalizedWeights` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L40 [advisory] `existential-packaging` in `def switchMatrix` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L46 [soft] `simp-law-injection` in `simp-declaration switchMatrix_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L57 [soft] `skeletal-proof` in `lemma switchMatrix_row_sum_one` — proof appears to close via minimal tactic one-liner
  - L96 [advisory] `existential-packaging` in `theorem exists_perm_decomposition_of_bistochastic` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L110 [advisory] `existential-packaging` in `structure SinkhornCertificate` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L115 [soft] `law-field-locker` in `structure-field SinkhornCertificate.leftScale` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L116 [soft] `law-field-locker` in `structure-field SinkhornCertificate.rightScale` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L117 [soft] `law-field-locker` in `structure-field SinkhornCertificate.leftScale_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L118 [soft] `law-field-locker` in `structure-field SinkhornCertificate.rightScale_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L124 [advisory] `existential-packaging` in `def SinkhornCertificate.ofBistochastic` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L133 [advisory] `local-hypothesis-injection` in `def SinkhornCertificate.ofBistochastic` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L138 [advisory] `existential-packaging` in `theorem exists_perm_decomposition_of_sinkhornBalanced` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L155 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L348 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L429 [advisory] `existential-packaging` in `def SinkhornStep` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L560 [soft] `law-field-locker` in `structure-field SinkhornTrajectory.state` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L561 [soft] `law-field-locker` in `structure-field SinkhornTrajectory.step` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L590 [soft] `skeletal-proof` in `theorem trajectoryLyapunov_monotone` — proof appears to close via minimal tactic one-liner
  - L607 [soft] `skeletal-proof` in `theorem trajectoryRNBarrier_monotone` — proof appears to close via minimal tactic one-liner
  - L620 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L640 [soft] `simp-law-injection` in `simp-declaration sinkhornScaledCoupling_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L675 [soft] `skeletal-proof` in `lemma entropicOptimalTransportObjective_eq_transport_plus_entropy` — proof appears to close via minimal tactic one-liner
  - L681 [soft] `simp-law-injection` in `simp-declaration bayesianFreeEnergyObjective_eq_regularizedOTObjective` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L725 [soft] `skeletal-proof` in `lemma sinkhornTwoStep_eq_twoSidedGauge` — proof appears to close via minimal tactic one-liner
  - L739 [soft] `skeletal-proof` in `lemma sinkhornTwoStep_eq_bayesianPosteriorGauge` — proof appears to close via minimal tactic one-liner
  - L753 [soft] `skeletal-proof` in `lemma sinkhornTwoStep_eq_schroedingerBridgeGauge` — proof appears to close via minimal tactic one-liner

