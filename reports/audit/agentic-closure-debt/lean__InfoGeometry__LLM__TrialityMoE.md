# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:58.502839+00:00`
Root: `lean/InfoGeometry/LLM/TrialityMoE.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **51**
- Hard: **0**
- Soft: **36**
- Advisory: **15**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/LLM/TrialityMoE.lean` | `advisory` | 87 | 0 | 36 | 15 | 51 |

## Findings by file

### `lean/InfoGeometry/LLM/TrialityMoE.lean`
- module: `InfoGeometry.LLM.TrialityMoE`
- status: `advisory`
- debt_score: `87`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L25 [soft] `law-field-locker` in `structure-field TwoStageResidualBlock.attentionNorm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L26 [soft] `law-field-locker` in `structure-field TwoStageResidualBlock.feedForwardNorm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L27 [soft] `law-field-locker` in `structure-field TwoStageResidualBlock.attention` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L28 [soft] `law-field-locker` in `structure-field TwoStageResidualBlock.feedForward` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `skeletal-proof` in `theorem two_stage_residual_block_update` — proof appears to close via minimal tactic one-liner
  - L66 [soft] `law-field-locker` in `structure-field SparseRouter.weight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field SparseRouter.gate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `law-field-locker` in `structure-field SparseRouter.inactive_weight_eq_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L93 [soft] `simp-law-injection` in `simp-declaration activeWeight_eq_weight` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L103 [soft] `simp-law-injection` in `simp-declaration defectWeight_eq_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L120 [soft] `law-field-locker` in `structure-field TrialityMoEBlock.router` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L121 [soft] `law-field-locker` in `structure-field TrialityMoEBlock.expert` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L164 [soft] `simp-law-injection` in `simp-declaration defectOutput_eq_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L173 [soft] `skeletal-proof` in `theorem totalOutput_eq_activeOutput` — proof appears to close via minimal tactic one-liner
  - L189 [soft] `law-field-locker` in `structure-field SharedRoutedMoEBlock.shared` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L190 [soft] `law-field-locker` in `structure-field SharedRoutedMoEBlock.routed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L229 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L231 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L241 [soft] `law-field-locker` in `structure-field RouterDefectBridge.residual_eq_observerDefect` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L262 [soft] `simp-law-injection` in `simp-declaration ofCanonicalObserverDefect_routerResidual` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L302 [soft] `law-field-locker` in `structure-field RouterDefectBoundBridge.residual_norm_le_ZD` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L318 [advisory] `existential-packaging` in `structure WeylThermodynamicOperatorComparison` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L323 [soft] `law-field-locker` in `structure-field WeylThermodynamicOperatorComparison.operatorInformationNormReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L327 [soft] `law-field-locker` in `structure-field WeylThermodynamicOperatorComparison.residual_readout_eq_relativeInformationNorm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L331 [soft] `law-field-locker` in `structure-field WeylThermodynamicOperatorComparison.central_readout_eq_relativeInformationNorm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L370 [advisory] `existential-packaging` in `structure WeylThermodynamicProfileComparison` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L375 [soft] `law-field-locker` in `structure-field WeylThermodynamicProfileComparison.operatorInformationNormReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L377 [soft] `law-field-locker` in `structure-field WeylThermodynamicProfileComparison.defectScale_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L380 [soft] `law-field-locker` in `structure-field WeylThermodynamicProfileComparison.residual_readout_eq_scaled_informationGeometricRelativeNorm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L414 [advisory] `existential-packaging` in `def ObserverDefectResidualWeylThermodynamicBoundedByZD` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L452 [soft] `law-field-locker` in `structure-field RouterDefectThermodynamicBridge.residual_eq_observerDefect` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L454 [soft] `law-field-locker` in `structure-field RouterDefectThermodynamicBridge.comparison` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L483 [soft] `simp-law-injection` in `simp-declaration ofCanonicalObserverDefect_routerResidual` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L584 [soft] `simp-law-injection` in `simp-declaration ofCompressedDeviationZeroObserver_routerResidual` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L594 [advisory] `local-hypothesis-injection` in `def ofCompressedDeviationZeroObserver` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L597 [soft] `simp-law-injection` in `simp-declaration ofZDControlledObserver_routerResidual_eq_zero_of_ZD_eq_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L611 [advisory] `local-hypothesis-injection` in `def ofCompressedDeviationZeroObserver` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L616 [soft] `simp-law-injection` in `simp-declaration ofCanonicalObserverDefect_routerResidual` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L667 [soft] `simp-law-injection` in `simp-declaration ofDeviationZeroObserver_routerResidual` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L674 [advisory] `local-hypothesis-injection` in `def ofDeviationZeroObserver` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L677 [soft] `simp-law-injection` in `simp-declaration ofStrainZeroObserver_routerResidual` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L684 [advisory] `local-hypothesis-injection` in `def ofDeviationZeroObserver` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L687 [soft] `simp-law-injection` in `simp-declaration ofAlignedObserver_routerResidual` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L694 [advisory] `local-hypothesis-injection` in `def ofDeviationZeroObserver` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L715 [advisory] `local-hypothesis-injection` in `theorem ofZDControlledObserver_sourcedGenerator_eq_flow_of_ZD_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L752 [advisory] `local-hypothesis-injection` in `theorem ofDeviationZeroObserver_sourcedGenerator_eq_flow` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L784 [advisory] `local-hypothesis-injection` in `theorem ofAlignedObserver_sourcedGenerator_eq_flow` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L816 [advisory] `local-hypothesis-injection` in `theorem ofStrainZeroObserver_sourcedGenerator_eq_flow` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L842 [soft] `skeletal-proof` in `theorem ofCanonicalObserverDefect_sourcedGenerator_eq_canonical` — proof appears to close via minimal tactic one-liner
  - L870 [soft] `skeletal-proof` in `theorem sourcedGenerator_deviation_norm_le_ZD` — proof appears to close via minimal tactic one-liner

