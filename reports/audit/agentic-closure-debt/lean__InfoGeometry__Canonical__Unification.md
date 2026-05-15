# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:08.345087+00:00`
Root: `lean/InfoGeometry/Canonical/Unification.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **22**
- Hard: **0**
- Soft: **18**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/Unification.lean` | `advisory` | 40 | 0 | 18 | 4 | 22 |

## Findings by file

### `lean/InfoGeometry/Canonical/Unification.lean`
- module: `InfoGeometry.Canonical.Unification`
- status: `advisory`
- debt_score: `40`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L25 [soft] `law-field-locker` in `structure-field AnomalyRosettaStone.einsteinAnomaly` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L27 [soft] `law-field-locker` in `structure-field AnomalyRosettaStone.fockDeformation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L30 [soft] `law-field-locker` in `structure-field AnomalyRosettaStone.modularGenerator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L33 [soft] `law-field-locker` in `structure-field AnomalyRosettaStone.liftToFock` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L36 [soft] `law-field-locker` in `structure-field AnomalyRosettaStone.embedToMajorana` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L38 [soft] `law-field-locker` in `structure-field AnomalyRosettaStone.h_geo_thermo` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L41 [soft] `law-field-locker` in `structure-field AnomalyRosettaStone.h_thermo_alg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L47 [soft] `section-law-variable` in `variable R` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L107 [soft] `law-field-locker` in `structure-field ScalarAnomalyRosettaStone.modularGenerator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L109 [soft] `law-field-locker` in `structure-field ScalarAnomalyRosettaStone.embedToMajorana` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L112 [soft] `law-field-locker` in `structure-field ScalarAnomalyRosettaStone.h_source_fock` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L113 [soft] `law-field-locker` in `structure-field ScalarAnomalyRosettaStone.h_fock_mod` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L116 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L116 [soft] `section-law-variable` in `variable S` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L208 [soft] `law-field-locker` in `structure-field Cl11LatticeRosettaStone.symmetry` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L210 [soft] `law-field-locker` in `structure-field Cl11LatticeRosettaStone.continuousAnomaly` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L212 [soft] `law-field-locker` in `structure-field Cl11LatticeRosettaStone.latticeAnomaly` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L214 [soft] `law-field-locker` in `structure-field Cl11LatticeRosettaStone.h_transport` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L239 [soft] `skeletal-proof` in `theorem latticeAvatar_canonicalContinuousCl11Anomaly` — proof appears to close via minimal tactic one-liner
  - L271 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

