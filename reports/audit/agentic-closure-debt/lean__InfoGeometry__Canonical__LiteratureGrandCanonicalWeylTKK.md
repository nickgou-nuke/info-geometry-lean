# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:25.742492+00:00`
Root: `lean/InfoGeometry/Canonical/LiteratureGrandCanonicalWeylTKK.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **44**
- Hard: **0**
- Soft: **32**
- Advisory: **12**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/LiteratureGrandCanonicalWeylTKK.lean` | `advisory` | 76 | 0 | 32 | 12 | 44 |

## Findings by file

### `lean/InfoGeometry/Canonical/LiteratureGrandCanonicalWeylTKK.lean`
- module: `InfoGeometry.Canonical.LiteratureGrandCanonicalWeylTKK`
- status: `advisory`
- debt_score: `76`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L53 [soft] `law-field-locker` in `structure-field ResidueContourHolonomyData.residueField` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L89 [soft] `law-field-locker` in `structure-field SimplePoleResidueData.inverseTemperature_eq_four_pi_residue` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L93 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L120 [soft] `skeletal-proof` in `theorem grandCanonicalSingularAction_eq` — proof appears to close via minimal tactic one-liner
  - L131 [soft] `skeletal-proof` in `theorem grandCanonicalSingularAction_eq_canonical_sub_muN` — proof appears to close via minimal tactic one-liner
  - L144 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L176 [soft] `skeletal-proof` in `theorem grandCanonicalContourHolonomyAction_eq_canonical_sub_muN` — proof appears to close via minimal tactic one-liner
  - L200 [soft] `law-field-locker` in `structure-field TolmanKleinRedshiftData.redshift` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L201 [soft] `law-field-locker` in `structure-field TolmanKleinRedshiftData.localTemperature` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L202 [soft] `law-field-locker` in `structure-field TolmanKleinRedshiftData.localChemicalPotential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L205 [soft] `law-field-locker` in `structure-field TolmanKleinRedshiftData.temperature_redshift` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L207 [soft] `law-field-locker` in `structure-field TolmanKleinRedshiftData.chemicalPotential_redshift` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L242 [soft] `law-field-locker` in `structure-field WeylGaugeCovariantInterface.transform` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L243 [soft] `law-field-locker` in `structure-field WeylGaugeCovariantInterface.curvature` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L244 [soft] `law-field-locker` in `structure-field WeylGaugeCovariantInterface.curvature_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L251 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L275 [soft] `law-field-locker` in `structure-field TKKThreeGradedClosure.bracket` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L276 [soft] `law-field-locker` in `structure-field TKKThreeGradedClosure.inGPlus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L277 [soft] `law-field-locker` in `structure-field TKKThreeGradedClosure.inGZero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L278 [soft] `law-field-locker` in `structure-field TKKThreeGradedClosure.inGMinus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L279 [soft] `law-field-locker` in `structure-field TKKThreeGradedClosure.bracket_plus_minus_mem_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L281 [soft] `law-field-locker` in `structure-field TKKThreeGradedClosure.bracket_zero_plus_mem_plus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L283 [soft] `law-field-locker` in `structure-field TKKThreeGradedClosure.bracket_zero_minus_mem_minus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L285 [soft] `law-field-locker` in `structure-field TKKThreeGradedClosure.bracket_zero_zero_mem_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L334 [soft] `law-field-locker` in `structure-field KarushKuhnTuckerThermodynamicData.primalFeasible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L335 [soft] `law-field-locker` in `structure-field KarushKuhnTuckerThermodynamicData.dualFeasible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L336 [soft] `law-field-locker` in `structure-field KarushKuhnTuckerThermodynamicData.stationarity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L337 [soft] `law-field-locker` in `structure-field KarushKuhnTuckerThermodynamicData.complementarySlackness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L338 [soft] `law-field-locker` in `structure-field KarushKuhnTuckerThermodynamicData.finitePartitionAdmissible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L341 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L346 [advisory] `bridge-shaped-declaration` in `theorem packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L374 [soft] `law-field-locker` in `structure-field KarushKuhnTuckerResidualCertificate.primalResidual_sq_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L375 [soft] `law-field-locker` in `structure-field KarushKuhnTuckerResidualCertificate.dualResidual_sq_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L376 [soft] `law-field-locker` in `structure-field KarushKuhnTuckerResidualCertificate.stationarityResidual_sq_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L377 [soft] `law-field-locker` in `structure-field KarushKuhnTuckerResidualCertificate.complementarySlacknessResidual_sq_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L379 [soft] `law-field-locker` in `structure-field KarushKuhnTuckerResidualCertificate.partitionResidual_sq_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L382 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L666 [advisory] `bridge-shaped-declaration` in `theorem entropyFoliation_transverseOnsager_weylCovariant_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L694 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L694 [soft] `section-law-variable` in `variable moment` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L702 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L718 [advisory] `bridge-shaped-declaration` in `theorem squareEntropyFoliation_transverseOnsager_weylCovariant_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

