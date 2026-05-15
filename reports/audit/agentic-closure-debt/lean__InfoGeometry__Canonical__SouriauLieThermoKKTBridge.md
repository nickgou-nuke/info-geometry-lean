# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:57.406060+00:00`
Root: `lean/InfoGeometry/Canonical/SouriauLieThermoKKTBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **61**
- Hard: **0**
- Soft: **41**
- Advisory: **20**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SouriauLieThermoKKTBridge.lean` | `advisory` | 102 | 0 | 41 | 20 | 61 |

## Findings by file

### `lean/InfoGeometry/Canonical/SouriauLieThermoKKTBridge.lean`
- module: `InfoGeometry.Canonical.SouriauLieThermoKKTBridge`
- status: `advisory`
- debt_score: `102`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L58 [soft] `law-field-locker` in `structure-field KKTEntropyStationarityShadow.coneAdmissible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L59 [soft] `law-field-locker` in `structure-field KKTEntropyStationarityShadow.stationarity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [soft] `law-field-locker` in `structure-field KKTEntropyStationarityShadow.complementarySlackness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L61 [soft] `law-field-locker` in `structure-field KKTEntropyStationarityShadow.finitePartitionAdmissible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [advisory] `bridge-shaped-declaration` in `theorem packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L96 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L135 [advisory] `bridge-shaped-declaration` in `theorem exact_stationarity_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L151 [soft] `skeletal-proof` in `theorem mk_exact` — proof appears to close via minimal tactic one-liner
  - L179 [soft] `law-field-locker` in `structure-field SuperCoadjointMomentMapData.coadjointAction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L180 [soft] `law-field-locker` in `structure-field SuperCoadjointMomentMapData.moment` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L182 [soft] `law-field-locker` in `structure-field SuperCoadjointMomentMapData.pairing` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L183 [soft] `law-field-locker` in `structure-field SuperCoadjointMomentMapData.parityOfGenerator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L184 [soft] `law-field-locker` in `structure-field SuperCoadjointMomentMapData.stressTensorProjection` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L185 [soft] `law-field-locker` in `structure-field SuperCoadjointMomentMapData.supercurrentProjection` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L186 [soft] `law-field-locker` in `structure-field SuperCoadjointMomentMapData.isOnCoadjointOrbit` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L191 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L210 [soft] `skeletal-proof` in `theorem actionAt_eq_pairing` — proof appears to close via minimal tactic one-liner
  - L226 [advisory] `existential-packaging` in `def identityBalanced` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L244 [soft] `skeletal-proof` in `theorem identityBalanced_coadjointAction` — proof appears to close via minimal tactic one-liner
  - L290 [soft] `law-field-locker` in `structure-field FullCoadjointOrbitMetriplecticContext.reversibleFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L291 [soft] `law-field-locker` in `structure-field FullCoadjointOrbitMetriplecticContext.dissipativeFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L292 [soft] `law-field-locker` in `structure-field FullCoadjointOrbitMetriplecticContext.entropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L293 [soft] `law-field-locker` in `structure-field FullCoadjointOrbitMetriplecticContext.reversibleEntropyRate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L294 [soft] `law-field-locker` in `structure-field FullCoadjointOrbitMetriplecticContext.dissipativeEntropyRate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L295 [soft] `law-field-locker` in `structure-field FullCoadjointOrbitMetriplecticContext.totalEntropyProduction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L296 [soft] `law-field-locker` in `structure-field FullCoadjointOrbitMetriplecticContext.moment_mem_orbit` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L299 [soft] `law-field-locker` in `structure-field FullCoadjointOrbitMetriplecticContext.reversible_preserves_orbit` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L303 [soft] `law-field-locker` in `structure-field FullCoadjointOrbitMetriplecticContext.orbit_entropy_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L306 [soft] `law-field-locker` in `structure-field FullCoadjointOrbitMetriplecticContext.reversibleEntropyRate_eq_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L309 [soft] `law-field-locker` in `structure-field FullCoadjointOrbitMetriplecticContext.dissipativeEntropyRate_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L312 [soft] `law-field-locker` in `structure-field FullCoadjointOrbitMetriplecticContext.totalEntropyProduction_eq_sum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L317 [soft] `law-field-locker` in `structure-field FullCoadjointOrbitMetriplecticContext.weyl_covariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L322 [soft] `law-field-locker` in `structure-field FullCoadjointOrbitMetriplecticContext.supertrace_balance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L439 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L507 [advisory] `bridge-shaped-declaration` in `theorem full_moment_image_square_dissipation_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L562 [advisory] `bridge-shaped-declaration` in `theorem full_identity_balanced_square_dissipation_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L666 [soft] `law-field-locker` in `structure-field CoordinatelessKMSFisherState.state` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L668 [soft] `law-field-locker` in `structure-field CoordinatelessKMSFisherState.kmsEquilibrium` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L669 [soft] `law-field-locker` in `structure-field CoordinatelessKMSFisherState.weylAutomorphismInvariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L671 [soft] `law-field-locker` in `structure-field CoordinatelessKMSFisherState.quantumFisherMetric_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L677 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L689 [advisory] `bridge-shaped-declaration` in `theorem algebraic_equilibrium_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L709 [advisory] `existential-packaging` in `structure SouriauLieThermoKKTContext` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L710 [soft] `law-field-locker` in `structure-field SouriauLieThermoKKTContext.finiteFenchel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L711 [soft] `law-field-locker` in `structure-field SouriauLieThermoKKTContext.finiteMetriplectic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L712 [soft] `law-field-locker` in `structure-field SouriauLieThermoKKTContext.conformalKKT` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L713 [soft] `law-field-locker` in `structure-field SouriauLieThermoKKTContext.operatorialMetriplectic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L715 [soft] `law-field-locker` in `structure-field SouriauLieThermoKKTContext.fenchel_metriplectic_moment` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L718 [soft] `law-field-locker` in `structure-field SouriauLieThermoKKTContext.fenchel_metriplectic_temperature` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L721 [soft] `law-field-locker` in `structure-field SouriauLieThermoKKTContext.conformal_metriplectic_moment` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L724 [soft] `law-field-locker` in `structure-field SouriauLieThermoKKTContext.conformal_metriplectic_temperature` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L731 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L731 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L732 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L734 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L735 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L1244 [advisory] `bridge-shaped-declaration` in `theorem operatorialSouriauFisherMetric_packet_of_cramerRaoResponse` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L1289 [advisory] `bridge-shaped-declaration` in `theorem operatorialSupergradedEvenOddOnsagerBlock_packet_of_cramerRaoResponse` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L1341 [advisory] `bridge-shaped-declaration` in `theorem kktStationarity_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L1354 [advisory] `bridge-shaped-declaration` in `theorem kktStationarity_packet_of_exact` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

