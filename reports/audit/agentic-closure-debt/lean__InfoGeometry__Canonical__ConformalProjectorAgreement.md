# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:55.567273+00:00`
Root: `lean/InfoGeometry/Canonical/ConformalProjectorAgreement.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **10**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ConformalProjectorAgreement.lean` | `advisory` | 22 | 0 | 10 | 2 | 12 |

## Findings by file

### `lean/InfoGeometry/Canonical/ConformalProjectorAgreement.lean`
- module: `InfoGeometry.Canonical.ConformalProjectorAgreement`
- status: `advisory`
- debt_score: `22`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L27 [soft] `law-field-locker` in `structure-field DrazinSimilarityTransportWitness.leftInv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L28 [soft] `law-field-locker` in `structure-field DrazinSimilarityTransportWitness.rightInv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L29 [soft] `law-field-locker` in `structure-field DrazinSimilarityTransportWitness.drazinProjector_transport` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L46 [soft] `law-field-locker` in `structure-field MoorePenroseMetricTransportWitness.metricTransportWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [soft] `law-field-locker` in `structure-field MoorePenroseMetricTransportWitness.moorePenroseProjector_transport` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [soft] `law-field-locker` in `structure-field ConformalMismatchTransportWitness.drazinTransport` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L75 [soft] `law-field-locker` in `structure-field ConformalMismatchTransportWitness.mpMetricTransport` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L76 [soft] `law-field-locker` in `structure-field ConformalMismatchTransportWitness.mismatchTransport` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L77 [soft] `law-field-locker` in `structure-field ConformalMismatchTransportWitness.commutatorTransport` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L113 [soft] `law-field-locker` in `structure-field FixedMetricMismatchDecompositionWitness.decomposition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L135 [advisory] `existential-packaging` in `def moorePenrose_not_generic_similarity_equivariant_under_fixed_metric` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

