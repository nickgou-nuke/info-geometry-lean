# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:44.397870+00:00`
Root: `lean/InfoGeometry/SuperMetriplectic/SupervolumeFunctional.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **17**
- Hard: **0**
- Soft: **16**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/SuperMetriplectic/SupervolumeFunctional.lean` | `advisory` | 33 | 0 | 16 | 1 | 17 |

## Findings by file

### `lean/InfoGeometry/SuperMetriplectic/SupervolumeFunctional.lean`
- module: `InfoGeometry.SuperMetriplectic.SupervolumeFunctional`
- status: `advisory`
- debt_score: `33`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L40 [soft] `law-field-locker` in `structure-field BerezinianSchurPacket.detDInv_is_inverse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L42 [soft] `law-field-locker` in `structure-field BerezinianSchurPacket.schurComplementDet_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L44 [soft] `law-field-locker` in `structure-field BerezinianSchurPacket.berezinianReg_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L73 [soft] `law-field-locker` in `structure-field ZetaRegularizedDeterminantPacket.logDetReg_eq_neg_zetaDerivative` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L75 [soft] `law-field-locker` in `structure-field ZetaRegularizedDeterminantPacket.casimirResidual_is_zeta_residue` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L107 [soft] `law-field-locker` in `structure-field RegularizedPfaffianPacket.weylVariation_eq_topologicalCharge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L109 [soft] `law-field-locker` in `structure-field RegularizedPfaffianPacket.topologicalCharge_eq_centralCharge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L148 [soft] `law-field-locker` in `structure-field SupervolumeFunctionalPacket.partitionFunctional_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L150 [soft] `law-field-locker` in `structure-field SupervolumeFunctionalPacket.entropyReadout_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L183 [soft] `law-field-locker` in `structure-field InformationSuperGasSupervolumeCapstone.characterPartition_matches_supervolume` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L246 [soft] `law-field-locker` in `structure-field SplitSupervolumeShadow.operator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L247 [soft] `law-field-locker` in `structure-field SplitSupervolumeShadow.supertraceReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L248 [soft] `law-field-locker` in `structure-field SplitSupervolumeShadow.superBerezinianReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L249 [soft] `law-field-locker` in `structure-field SplitSupervolumeShadow.supervolumePotential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L250 [soft] `simp-law-injection` in `simp-declaration supervolumePotential_eq_neg_log_superBerezinian` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L252 [soft] `skeletal-proof` in `theorem supervolumePotential_eq_neg_log_superBerezinian` — proof appears to close via minimal tactic one-liner

