# Semantic De-dup Audit (Lean)

- Lean files scanned: 1022

## Concept totals (token-level)
- anomaly: 539 hits in 109 files
- chiral: 545 hits in 133 files
- cl44: 61 hits in 19 files
- conformal: 276 hits in 43 files
- dilation: 194 hits in 62 files
- drazin: 897 hits in 135 files
- einstein: 167 hits in 36 files
- moore_penrose: 525 hits in 145 files
- noncommutativity: 74 hits in 39 files
- projector: 1068 hits in 176 files
- weyl: 547 hits in 100 files

## Axis intersections (file-level)
- projector_pseudoinverse_axis: 54 files
- anomaly_response_axis: 16 files
- chiral_gravity_readout_axis: 4 files
- noncomm_closure_axis: 0 files

## High-overlap files (>=4 concept groups)
- lean/InfoGeometry/Canonical/AnomalyOwnerMap.lean :: 9 groups :: anomaly, drazin, moore_penrose, projector, conformal, dilation, chiral, weyl, cl44
- lean/InfoGeometry/Canonical/ConformalAnomalySource.lean :: 9 groups :: anomaly, drazin, moore_penrose, projector, conformal, dilation, noncommutativity, chiral, einstein
- lean/InfoGeometry/Canonical/PhaseSpaceWeylCausalBridge.lean :: 9 groups :: anomaly, drazin, moore_penrose, projector, conformal, dilation, chiral, weyl, einstein
- lean/InfoGeometry/Canonical/ConformalProjectorCore.lean :: 8 groups :: anomaly, drazin, moore_penrose, projector, conformal, dilation, chiral, einstein
- lean/InfoGeometry/Canonical/MasterSynthesis.lean :: 8 groups :: anomaly, drazin, moore_penrose, projector, conformal, chiral, weyl, einstein
- lean/InfoGeometry/Canonical/ResponseWeylAnomalyBridge.lean :: 8 groups :: anomaly, drazin, moore_penrose, projector, conformal, noncommutativity, chiral, weyl
- lean/InfoGeometry/Canonical/BerryConnection.lean :: 7 groups :: anomaly, moore_penrose, projector, conformal, dilation, weyl, einstein
- lean/InfoGeometry/Canonical/ConformalAnomalyOperator.lean :: 7 groups :: anomaly, drazin, moore_penrose, projector, conformal, dilation, noncommutativity
- lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean :: 7 groups :: anomaly, drazin, moore_penrose, projector, conformal, chiral, einstein
- lean/InfoGeometry/Canonical/WeylKKTAnomalyIdentity.lean :: 7 groups :: anomaly, projector, conformal, dilation, chiral, weyl, einstein
- lean/InfoGeometry/Quantum/HestenesKahler.lean :: 7 groups :: anomaly, moore_penrose, projector, conformal, dilation, weyl, einstein
- lean/InfoGeometry/Canonical/AnomalyDilationBridge.lean :: 6 groups :: anomaly, moore_penrose, projector, conformal, dilation, chiral
- lean/InfoGeometry/Canonical/BerryPhase.lean :: 6 groups :: anomaly, drazin, moore_penrose, projector, chiral, weyl
- lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean :: 6 groups :: anomaly, drazin, moore_penrose, projector, conformal, dilation
- lean/InfoGeometry/Canonical/ChiralCliffordBridge.lean :: 6 groups :: anomaly, drazin, moore_penrose, projector, conformal, chiral
- lean/InfoGeometry/Canonical/DrazinPenroseDilationKKT.lean :: 6 groups :: anomaly, drazin, moore_penrose, projector, dilation, chiral
- lean/InfoGeometry/Canonical/GenerativeInferenceCore.lean :: 6 groups :: anomaly, drazin, moore_penrose, projector, chiral, weyl
- lean/InfoGeometry/Canonical/GrandUnificationBlueprint.lean :: 6 groups :: anomaly, drazin, moore_penrose, projector, noncommutativity, chiral
- lean/InfoGeometry/Canonical/IncompressibleCramerRaoActionBridge.lean :: 6 groups :: anomaly, projector, conformal, dilation, chiral, weyl
- lean/InfoGeometry/Canonical/NavierStokesBridge.lean :: 6 groups :: anomaly, drazin, moore_penrose, projector, chiral, einstein
- lean/InfoGeometry/Canonical/PhaseSpaceCausalFlowBridge.lean :: 6 groups :: drazin, moore_penrose, projector, conformal, dilation, chiral
- lean/InfoGeometry/Canonical/PhaseSpaceConformalKKTBridge.lean :: 6 groups :: drazin, moore_penrose, projector, conformal, dilation, chiral
- lean/InfoGeometry/Canonical/Singular.lean :: 6 groups :: anomaly, drazin, moore_penrose, projector, chiral, einstein
- lean/InfoGeometry/Canonical/SingularBoundaryCorrection.lean :: 6 groups :: anomaly, drazin, moore_penrose, projector, dilation, weyl
- lean/InfoGeometry/Canonical/SouriauLieThermoKKTBridge.lean :: 6 groups :: drazin, conformal, dilation, noncommutativity, chiral, weyl

## Notes
- This is lexical co-occurrence, not proof equivalence.
- `mp` token can be noisy; Moore-Penrose counts are upper-bounded by lexical ambiguity.