# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:48.553557+00:00`
Root: `lean/InfoGeometry/Canonical/RealHomologyCohomologyDictionary.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **39**
- Hard: **0**
- Soft: **20**
- Advisory: **19**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RealHomologyCohomologyDictionary.lean` | `advisory` | 59 | 0 | 20 | 19 | 39 |

## Findings by file

### `lean/InfoGeometry/Canonical/RealHomologyCohomologyDictionary.lean`
- module: `InfoGeometry.Canonical.RealHomologyCohomologyDictionary`
- status: `advisory`
- debt_score: `59`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L48 [soft] `law-field-locker` in `structure-field RealBoundaryOperator.d` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `law-field-locker` in `structure-field RealBoundaryOperator.d_sq_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L64 [advisory] `existential-packaging` in `def IsBoundary` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L94 [soft] `skeletal-proof` in `theorem homologyEquivalent_symm` — proof appears to close via minimal tactic one-liner
  - L108 [soft] `skeletal-proof` in `theorem homologyEquivalent_trans` — proof appears to close via minimal tactic one-liner
  - L140 [soft] `law-field-locker` in `structure-field BoundaryVanishingWitness.eval` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L141 [soft] `law-field-locker` in `structure-field BoundaryVanishingWitness.vanishes_on_boundaries` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L147 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L157 [advisory] `local-hypothesis-injection` in `theorem descends_to_homology_equivalence` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L178 [soft] `law-field-locker` in `structure-field RealPairing.pairing` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L179 [soft] `law-field-locker` in `structure-field RealPairing.sub_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L187 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L208 [advisory] `local-hypothesis-injection` in `theorem pairing_descends_to_homology_equiv` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L224 [soft] `law-field-locker` in `structure-field PairingFrameTransport.transportChain` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L225 [soft] `law-field-locker` in `structure-field PairingFrameTransport.transportCochain` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L227 [soft] `law-field-locker` in `structure-field PairingFrameTransport.preserves_pairing` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L236 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L252 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L254 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L263 [advisory] `existential-packaging` in `def IsRealBoundary` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L294 [soft] `skeletal-proof` in `theorem homologyEquivalent_symm` — proof appears to close via minimal tactic one-liner
  - L308 [soft] `skeletal-proof` in `theorem homologyEquivalent_trans` — proof appears to close via minimal tactic one-liner
  - L392 [advisory] `bridge-shaped-declaration` in `theorem witness_descends_to_homologyEquivalent` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L400 [advisory] `local-hypothesis-injection` in `theorem witness_descends_to_homologyEquivalent` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L426 [soft] `skeletal-proof` in `theorem isModuleEndDrazinNullCycle_iff_mem_drazinCore` — proof appears to close via minimal tactic one-liner
  - L520 [soft] `law-field-locker` in `structure-field RealPairingSocket.pairing` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L521 [soft] `law-field-locker` in `structure-field RealPairingSocket.pairing_sub_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L527 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L527 [soft] `section-law-variable` in `variable P` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L587 [advisory] `local-hypothesis-injection` in `theorem pairing_eq_of_homologyEquivalent` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L590 [advisory] `local-hypothesis-injection` in `theorem pairing_eq_of_homologyEquivalent` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L610 [soft] `skeletal-proof` in `theorem transportedWitness_readout_eq` — proof appears to close via minimal tactic one-liner
  - L617 [advisory] `local-hypothesis-injection` in `theorem transportedWitness_readout_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L646 [soft] `law-field-locker` in `structure-field HestenesKreinFrameMap.preservesKrein` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L647 [soft] `law-field-locker` in `structure-field HestenesKreinFrameMap.preservesPhaseAxis` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L671 [advisory] `existential-packaging` in `def IsRealCoboundary` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L688 [advisory] `existential-packaging` in `def IsLinearRealCoboundary` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

