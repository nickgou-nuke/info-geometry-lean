# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:57.928141+00:00`
Root: `lean/InfoGeometry/Canonical/SouriauModularHamiltonianBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **24**
- Hard: **0**
- Soft: **20**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SouriauModularHamiltonianBridge.lean` | `advisory` | 44 | 0 | 20 | 4 | 24 |

## Findings by file

### `lean/InfoGeometry/Canonical/SouriauModularHamiltonianBridge.lean`
- module: `InfoGeometry.Canonical.SouriauModularHamiltonianBridge`
- status: `advisory`
- debt_score: `44`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L40 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L66 [soft] `law-field-locker` in `structure-field SouriauModularHamiltonianCarrier.superchargeBridge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [soft] `law-field-locker` in `structure-field SouriauModularHamiltonianCarrier.scalarBetaGauge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L104 [soft] `law-field-locker` in `structure-field SouriauModularHamiltonianBridge.superBridge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L109 [soft] `law-field-locker` in `structure-field SouriauModularHamiltonianBridge.Khat_beta_eq_Ksur` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L112 [soft] `law-field-locker` in `structure-field SouriauModularHamiltonianBridge.opAdd_eq_add` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L115 [soft] `law-field-locker` in `structure-field SouriauModularHamiltonianBridge.opScale_eq_smul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L118 [soft] `law-field-locker` in `structure-field SouriauModularHamiltonianBridge.opIdentity_eq_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L123 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L123 [soft] `section-law-variable` in `variable B` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L237 [soft] `skeletal-proof` in `theorem modularHamiltonian_commutes_GammaS` — proof appears to close via minimal tactic one-liner
  - L281 [soft] `law-field-locker` in `structure-field RealExpectationState.expect` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L282 [soft] `law-field-locker` in `structure-field RealExpectationState.unital` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L283 [soft] `law-field-locker` in `structure-field RealExpectationState.positive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L294 [soft] `law-field-locker` in `structure-field SouriauFreeEnergyOwner.freeEnergyObservable` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L295 [soft] `law-field-locker` in `structure-field SouriauFreeEnergyOwner.freeEnergy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L314 [soft] `law-field-locker` in `structure-field BoundedModularHamiltonianSurrogate.P_D_idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L315 [soft] `law-field-locker` in `structure-field BoundedModularHamiltonianSurrogate.P_D_self_adjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L316 [soft] `law-field-locker` in `structure-field BoundedModularHamiltonianSurrogate.Q_self_adjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L317 [soft] `law-field-locker` in `structure-field BoundedModularHamiltonianSurrogate.K_sur_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L322 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L345 [soft] `law-field-locker` in `structure-field IsOperatorCalibratedBySouriau.K_sur_eq_freeEnergyObservable` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L361 [soft] `law-field-locker` in `structure-field IsSouriauFreeEnergyReadoutCalibrated.expect_freeEnergyObservable_eq_freeEnergy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

