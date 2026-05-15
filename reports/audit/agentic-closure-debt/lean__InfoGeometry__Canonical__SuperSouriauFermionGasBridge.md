# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:03.123531+00:00`
Root: `lean/InfoGeometry/Canonical/SuperSouriauFermionGasBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **28**
- Hard: **0**
- Soft: **21**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SuperSouriauFermionGasBridge.lean` | `advisory` | 49 | 0 | 21 | 7 | 28 |

## Findings by file

### `lean/InfoGeometry/Canonical/SuperSouriauFermionGasBridge.lean`
- module: `InfoGeometry.Canonical.SuperSouriauFermionGasBridge`
- status: `advisory`
- debt_score: `49`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L39 [soft] `law-field-locker` in `structure-field SuperMomentMapData.evenMoment` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L40 [soft] `law-field-locker` in `structure-field SuperMomentMapData.oddMoment` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L41 [soft] `law-field-locker` in `structure-field SuperMomentMapData.stressTensorReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L42 [soft] `law-field-locker` in `structure-field SuperMomentMapData.chargeReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field SuperMomentMapData.supercurrentReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L66 [soft] `skeletal-proof` in `theorem stressTensor_eq_even_readout` — proof appears to close via minimal tactic one-liner
  - L70 [soft] `skeletal-proof` in `theorem supercurrent_eq_odd_readout` — proof appears to close via minimal tactic one-liner
  - L81 [advisory] `bridge-shaped-declaration` in `theorem projection_readout_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L106 [soft] `law-field-locker` in `structure-field SuperSouriauPairing.evenEnergy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L107 [soft] `law-field-locker` in `structure-field SuperSouriauPairing.oddSource` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L112 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L120 [soft] `skeletal-proof` in `theorem action_eq_even_add_odd` — proof appears to close via minimal tactic one-liner
  - L125 [soft] `skeletal-proof` in `theorem action_zero_odd_beta` — proof appears to close via minimal tactic one-liner
  - L160 [soft] `skeletal-proof` in `theorem superGrandCanonicalFockGenerator_eq_even_add_odd` — proof appears to close via minimal tactic one-liner
  - L174 [advisory] `local-hypothesis-injection` in `theorem superGrandCanonicalFockGenerator_zero_odd_beta` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L185 [soft] `skeletal-proof` in `theorem superGrandCanonicalFockGenerator_zero_mu` — proof appears to close via minimal tactic one-liner
  - L194 [soft] `skeletal-proof` in `theorem odd_odd_superBracket_eq_CARBracket` — proof appears to close via minimal tactic one-liner
  - L201 [soft] `skeletal-proof` in `theorem even_even_superBracket_eq_CCRBracket` — proof appears to close via minimal tactic one-liner
  - L217 [soft] `law-field-locker` in `structure-field FermionicCAROperatorPair.car` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L220 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L220 [soft] `section-law-variable` in `variable F` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L308 [advisory] `local-hypothesis-injection` in `theorem superFockConcreteFermionGasPacket` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L334 [soft] `law-field-locker` in `structure-field WeylSupertraceFreeStressContext.superTrace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L335 [soft] `law-field-locker` in `structure-field WeylSupertraceFreeStressContext.weylInvariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L336 [soft] `law-field-locker` in `structure-field WeylSupertraceFreeStressContext.stress_supertrace_free` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L426 [soft] `skeletal-proof` in `theorem superTrace_eq_zero_ofIdentityBalanced` — proof appears to close via minimal tactic one-liner

