# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:26.941662+00:00`
Root: `lean/InfoGeometry/Canonical/MajoranaKitaevSpinorBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **11**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/MajoranaKitaevSpinorBridge.lean` | `advisory` | 24 | 0 | 11 | 2 | 13 |

## Findings by file

### `lean/InfoGeometry/Canonical/MajoranaKitaevSpinorBridge.lean`
- module: `InfoGeometry.Canonical.MajoranaKitaevSpinorBridge`
- status: `advisory`
- debt_score: `24`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L46 [soft] `law-field-locker` in `structure-field WeylBoundarySpinorPair.psiPlus_weyl` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `law-field-locker` in `structure-field WeylBoundarySpinorPair.psiMinus_weyl` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [soft] `law-field-locker` in `structure-field WeylBoundarySpinorPair.psiPlus_zeroMode` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `law-field-locker` in `structure-field WeylBoundarySpinorPair.psiMinus_zeroMode` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L59 [soft] `law-field-locker` in `structure-field MajoranaKitaevSpinorRegularizationPackage.spinors` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [soft] `law-field-locker` in `structure-field MajoranaKitaevSpinorRegularizationPackage.Q_MP` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L61 [soft] `law-field-locker` in `structure-field MajoranaKitaevSpinorRegularizationPackage.Q_D` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `law-field-locker` in `structure-field MajoranaKitaevSpinorRegularizationPackage.rightProjector_ne_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field MajoranaKitaevSpinorRegularizationPackage.leftProjector_ne_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L69 [soft] `law-field-locker` in `structure-field MajoranaKitaevSpinorRegularizationPackage.drazinProjection_ne_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L104 [soft] `classical-witness-smuggling` in `def weylBoundarySpinorPair_of_nontrivial_chiralKernelSlices_of_identifiedChirality` — declaration uses Classical/choice/Nonempty witness extraction; require constructive payload readback or explicit nonconstructive boundary
  - L231 [advisory] `existential-packaging` in `theorem exists_nontrivial_regularization_pair_of_simplifiedBoundaryModel` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

