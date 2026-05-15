# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:15.293004+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/HorizonEschaton.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **54**
- Hard: **0**
- Soft: **27**
- Advisory: **27**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/HorizonEschaton.lean` | `advisory` | 81 | 0 | 27 | 27 | 54 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/HorizonEschaton.lean`
- module: `InfoGeometry.OperatorAlgebra.HorizonEschaton`
- status: `advisory`
- debt_score: `81`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L63 [soft] `law-field-locker` in `structure-field GenesisSplitDatum.toObservable` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `law-field-locker` in `structure-field GenesisSplitDatum.toHidden` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `law-field-locker` in `structure-field GenesisSplitDatum.boundaryOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L71 [soft] `law-field-locker` in `structure-field GenesisSplitDatum.split_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L86 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L106 [soft] `law-field-locker` in `structure-field HiddenMemoryLedger.observedDefect` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L107 [soft] `law-field-locker` in `structure-field HiddenMemoryLedger.hiddenMemory` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L112 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L135 [soft] `law-field-locker` in `structure-field HorizonEvaporationDatum.horizonEntropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L137 [soft] `law-field-locker` in `structure-field HorizonEvaporationDatum.evaporation_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L152 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L172 [soft] `law-field-locker` in `structure-field RevelationRecoveryDatum.exteriorDecode` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L175 [soft] `law-field-locker` in `structure-field RevelationRecoveryDatum.faithful_recovery` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L190 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L240 [soft] `law-field-locker` in `structure-field ExteriorCollapseWitness.same_observed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L253 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L254 [advisory] `existential-packaging` in `theorem no_faithful_recovery` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L292 [advisory] `existential-packaging` in `theorem no_faithful_recovery` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L322 [soft] `law-field-locker` in `structure-field PralayaDissolutionDatum.thermalize` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L327 [soft] `law-field-locker` in `structure-field PralayaDissolutionDatum.dissolution` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L336 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L360 [advisory] `existential-packaging` in `theorem no_two_point_recovery_after_dissolution` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L373 [advisory] `local-hypothesis-injection` in `theorem no_two_point_recovery_after_dissolution` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L380 [advisory] `local-hypothesis-injection` in `theorem no_two_point_recovery_after_dissolution` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L406 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L487 [soft] `law-field-locker` in `structure-field HolographicMemoryRetention.terminalize` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L489 [soft] `law-field-locker` in `structure-field HolographicMemoryRetention.memoryOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L492 [soft] `law-field-locker` in `structure-field HolographicMemoryRetention.readout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L495 [soft] `law-field-locker` in `structure-field HolographicMemoryRetention.faithful_terminal_readout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L505 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L519 [advisory] `existential-packaging` in `structure MahapralayaResetDatum` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L528 [soft] `law-field-locker` in `structure-field MahapralayaResetDatum.terminalize` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L530 [soft] `law-field-locker` in `structure-field MahapralayaResetDatum.memoryOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L533 [soft] `law-field-locker` in `structure-field MahapralayaResetDatum.readout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L539 [soft] `law-field-locker` in `structure-field MahapralayaResetDatum.terminal_readout_collapse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L544 [soft] `law-field-locker` in `structure-field MahapralayaResetDatum.nontrivial_memory` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L553 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L592 [soft] `law-field-locker` in `structure-field HolographicRetentionDatum.encode` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L597 [advisory] `existential-packaging` in `structure ComputationalResetDatum` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L606 [soft] `law-field-locker` in `structure-field ComputationalResetDatum.encode` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L611 [soft] `law-field-locker` in `structure-field ComputationalResetDatum.collapse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L616 [soft] `law-field-locker` in `structure-field ComputationalResetDatum.nontrivialMemory` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L625 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L654 [soft] `law-field-locker` in `structure-field HorizonProcessClassification.classification_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L656 [advisory] `existential-packaging` in `def GenesisQuenchOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L665 [advisory] `existential-packaging` in `def RevelationRecoveryOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L673 [advisory] `existential-packaging` in `def PralayaDissolutionOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L680 [advisory] `existential-packaging` in `def EvaporationWithoutRecoveryOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L687 [advisory] `existential-packaging` in `def HorizonEschatonOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L694 [advisory] `existential-packaging` in `def HolographicMemoryRetentionOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L701 [advisory] `existential-packaging` in `def MahapralayaResetOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L708 [advisory] `existential-packaging` in `def HolographicRetentionOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L715 [advisory] `existential-packaging` in `def ComputationalResetOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

