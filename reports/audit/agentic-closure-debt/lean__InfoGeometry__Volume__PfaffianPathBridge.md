# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:51.364107+00:00`
Root: `lean/InfoGeometry/Volume/PfaffianPathBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **44**
- Hard: **0**
- Soft: **41**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Volume/PfaffianPathBridge.lean` | `advisory` | 85 | 0 | 41 | 3 | 44 |

## Findings by file

### `lean/InfoGeometry/Volume/PfaffianPathBridge.lean`
- module: `InfoGeometry.Volume.PfaffianPathBridge`
- status: `advisory`
- debt_score: `85`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L40 [soft] `law-field-locker` in `structure-field SourceSinkPathSystem.pathFintype` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L41 [soft] `law-field-locker` in `structure-field SourceSinkPathSystem.weight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L69 [soft] `law-field-locker` in `structure-field DeterminantPathExpansion.permSign` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L71 [soft] `law-field-locker` in `structure-field DeterminantPathExpansion.pathFamilyWeight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [soft] `law-field-locker` in `structure-field DeterminantPathExpansion.pathFamilyWeight_eq_product` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L104 [soft] `law-field-locker` in `structure-field LindstromGesselViennotWitness.weight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L121 [soft] `law-field-locker` in `structure-field FinitePathMatrix.weight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L170 [soft] `law-field-locker` in `structure-field SourceSinkPathFamilyCalibration.determinant_counts_pathFamilies` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L181 [soft] `law-field-locker` in `structure-field SkewPairingMatrix.weight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L182 [soft] `law-field-locker` in `structure-field SkewPairingMatrix.skew` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L206 [soft] `law-field-locker` in `structure-field PfaffianMatchingExpansion.pairingWeight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L207 [soft] `law-field-locker` in `structure-field PfaffianMatchingExpansion.matchingSign` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L209 [soft] `law-field-locker` in `structure-field PfaffianMatchingExpansion.signedMatchingSum_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L225 [soft] `law-field-locker` in `structure-field SkewPfaffianPathCalibration.pfaffian_eq_matching_sum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L228 [soft] `law-field-locker` in `structure-field SkewPfaffianPathCalibration.determinant_eq_pfaffian_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L262 [soft] `law-field-locker` in `structure-field PerfectMatchingExpansion.matchingSign` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L263 [soft] `law-field-locker` in `structure-field PerfectMatchingExpansion.matchingWeight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L287 [soft] `law-field-locker` in `structure-field SignedPfaffianSquareTheorem.pf_sq_eq_det` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L314 [soft] `law-field-locker` in `structure-field PositiveBranchPfaffianCompatibility.pf_pos_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L317 [soft] `law-field-locker` in `structure-field PositiveBranchPfaffianCompatibility.pf_pos_eq_abs_signed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L326 [soft] `law-field-locker` in `structure-field WeylKMSPairingWeight.weylWeight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L328 [soft] `law-field-locker` in `structure-field WeylKMSPairingWeight.kmsWeight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L329 [soft] `law-field-locker` in `structure-field WeylKMSPairingWeight.positive_weyl` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L332 [soft] `law-field-locker` in `structure-field WeylKMSPairingWeight.nonnegative_kms` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L343 [soft] `law-field-locker` in `structure-field PhysicalSkewPairing.raw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L347 [soft] `law-field-locker` in `structure-field PhysicalSkewPairing.weighted_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L396 [soft] `law-field-locker` in `structure-field MatterEnvelope.envelope_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L409 [soft] `law-field-locker` in `structure-field MatterEnvelopeBoundaryKernel.boundaryCoupling` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L411 [soft] `law-field-locker` in `structure-field MatterEnvelopeBoundaryKernel.skewCoupling_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L427 [soft] `law-field-locker` in `structure-field MatterEnvelopePfaffianDeterminant.pf_sq_det` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L460 [advisory] `existential-packaging` in `def PfaffianPathBridgeTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L496 [soft] `law-field-locker` in `structure-field FinitePathMatrixPacket.pathWeight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L497 [soft] `law-field-locker` in `structure-field FinitePathMatrixPacket.matrixWeight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L503 [soft] `law-field-locker` in `structure-field FinitePathMatrixPacket.determinant_eq_signedPathFamilyExpansion` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L522 [soft] `law-field-locker` in `structure-field SkewPairingMatrixPacket.pairWeight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L524 [soft] `law-field-locker` in `structure-field SkewPairingMatrixPacket.skew` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L539 [soft] `law-field-locker` in `structure-field PfaffianMatchingExpansionPacket.pairingSign` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L541 [soft] `law-field-locker` in `structure-field PfaffianMatchingExpansionPacket.pairingProductWeight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L546 [soft] `law-field-locker` in `structure-field PfaffianMatchingExpansionPacket.matchingExpansion_sumWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L552 [soft] `law-field-locker` in `structure-field PfaffianMatchingExpansionPacket.pfaffian_eq_matchingExpansion` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L555 [soft] `law-field-locker` in `structure-field PfaffianMatchingExpansionPacket.pfaffian_sq_eq_determinantEvenVolume` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L590 [soft] `law-field-locker` in `structure-field ChiralPathWordPacket.pathWordAmplitude` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L608 [advisory] `existential-packaging` in `def PfaffianPathBridgePacketTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

