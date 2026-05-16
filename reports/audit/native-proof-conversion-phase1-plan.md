# Native Proof Conversion — Phase 1 Plan (Easiest Witness-Gated Leftovers)

Date: 2026-05-16
Repo: /home/goutev/repos/info-geometry-lean
Mandate: replace easiest witness-gated AFP leftovers with native Lean proofs.

## Selection heuristic
- smallest modules first (line count)
- explicit witness-gated / deferred / externally-gated language present
- avoid large dependency fan-out in phase 1

## Phase 1 target set (top 8)
1. lean/InfoGeometry/Canonical/GeometricFreudenthalBoundary.lean (21 lines)
2. lean/InfoGeometry/Arithmetic/PrimeMajoranaWittenCharacter.lean (79 lines)
3. lean/InfoGeometry/Canonical/PrimeGasWeylCharacterBridge.lean (82 lines)
4. lean/InfoGeometry/OperatorAlgebra/AndreevHorizonBridge.lean (82 lines)
5. lean/InfoGeometry/OperatorAlgebra/BaryonAsymmetryWitness.lean (97 lines)
6. lean/InfoGeometry/Arithmetic/ProjectivePrimePartition.lean (100 lines)
7. lean/InfoGeometry/Canonical/PrimeGasSuperKMSBridge.lean (104 lines)
8. lean/InfoGeometry/Arithmetic/PrimeMajoranaOPE.lean (107 lines)

## Work protocol per module
1) Build baseline module target.
2) Read file and identify witness-gated theorem/definition surfaces.
3) Replace scaffold-only target with native theorem-backed owner/translator chain.
4) Keep any unresolved claim as explicit closure debt (exact premises -> target).
5) Rebuild module.
6) Record result and next blocker.

## Exit criteria
- phase-1 modules compile with native-proof closure replacing easiest witness leftovers where feasible
- no newly introduced placeholder debt
- unresolved items tracked as explicit closure-debt statements
