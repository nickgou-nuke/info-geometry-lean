# Semantic De-dup Map (Lean + Arango SCC anchors)

## Canonical concept families
- ProjectorPseudoinverseMismatch
  - canonical tokens: drazin, moore_penrose, projector
  - aliases (27): CI.D, Delta, Drazin spectral projector, DrazinPenroseDilationKKT.commutator, InfoGeometry.Canonical.ConformalUnification.ConformalInference.P_MP, InfoGeometry.Canonical.ConformalUnification.ConformalInference.P_MP_right, InfoGeometry.Canonical.DrazinPenroseDilationKKT.DPDKKT.Delta, InfoGeometry.Canonical.DrazinPenroseDilationKKT.DPDKKT.P_L, InfoGeometry.Canonical.DrazinPenroseDilationKKT.DPDKKT.P_R, InfoGeometry.Canonical.DrazinPenroseDilationKKT.DPDKKT.Q_D, InfoGeometry.Canonical.DrazinPenroseDilationKKT.DPDKKT.leftSupercharge, IsMoorePenroseInverse.leftProjector ...
- AnomalyToDilationResponse
  - canonical tokens: anomaly, dilation, conformal
  - aliases (23): CI.D, DrazinPenroseDilationKKT.commutator, InfoGeometry.Canonical.ConformalUnification.ConformalInference.P_MP, InfoGeometry.Canonical.ConformalUnification.ConformalInference.P_MP_right, InfoGeometry.Canonical.DrazinPenroseDilationKKT.DPDKKT.Delta, InfoGeometry.Canonical.DrazinPenroseDilationKKT.DPDKKT.P_L, InfoGeometry.Canonical.DrazinPenroseDilationKKT.DPDKKT.P_R, InfoGeometry.Canonical.DrazinPenroseDilationKKT.DPDKKT.Q_D, InfoGeometry.Canonical.DrazinPenroseDilationKKT.DPDKKT.leftSupercharge, IsMoorePenroseInverse.leftProjector, IsMoorePenroseInverse.rightProjector, K.kernel.leftAnomalyGenerator ...
- WeylChiralEinsteinReadout
  - canonical tokens: weyl, chiral, einstein
  - aliases (3): Einstein anomaly operator, Weyl transport, chiral scale/source
- Cl44ClosureReadout
  - canonical tokens: cl44, conformal, closure
  - aliases (3): JordanLieClosure, Spin(4,4) readout (textual), SplitCl44TKKJordanLiePacket

## Axis intersections (file-level)
- projector_pseudoinverse_axis: 54
- anomaly_response_axis: 16
- chiral_gravity_readout_axis: 4
- noncomm_closure_axis: 0

## Owner corridor candidates
- lean/InfoGeometry/Canonical/PhaseSpaceWeylCausalBridge.lean :: score=9 :: concepts=anomaly, drazin, moore_penrose, projector, conformal, dilation, chiral, weyl, einstein
- lean/InfoGeometry/Canonical/AnomalyOwnerMap.lean :: score=8 :: concepts=anomaly, drazin, moore_penrose, projector, conformal, dilation, chiral, weyl, cl44
- lean/InfoGeometry/Canonical/ConformalAnomalySource.lean :: score=8 :: concepts=anomaly, drazin, moore_penrose, projector, conformal, dilation, noncommutativity, chiral, einstein
- lean/InfoGeometry/Canonical/ConformalProjectorCore.lean :: score=8 :: concepts=anomaly, drazin, moore_penrose, projector, conformal, dilation, chiral, einstein
- lean/InfoGeometry/Canonical/MasterSynthesis.lean :: score=8 :: concepts=anomaly, drazin, moore_penrose, projector, conformal, chiral, weyl, einstein
- lean/InfoGeometry/Canonical/ResponseWeylAnomalyBridge.lean :: score=7 :: concepts=anomaly, drazin, moore_penrose, projector, conformal, noncommutativity, chiral, weyl
- lean/InfoGeometry/Canonical/BerryConnection.lean :: score=7 :: concepts=anomaly, moore_penrose, projector, conformal, dilation, weyl, einstein
- lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean :: score=7 :: concepts=anomaly, drazin, moore_penrose, projector, conformal, chiral, einstein
- lean/InfoGeometry/Canonical/WeylKKTAnomalyIdentity.lean :: score=7 :: concepts=anomaly, projector, conformal, dilation, chiral, weyl, einstein
- lean/InfoGeometry/Quantum/HestenesKahler.lean :: score=7 :: concepts=anomaly, moore_penrose, projector, conformal, dilation, weyl, einstein
- lean/InfoGeometry/Canonical/ConformalAnomalyOperator.lean :: score=6 :: concepts=anomaly, drazin, moore_penrose, projector, conformal, dilation, noncommutativity
- lean/InfoGeometry/Canonical/AnomalyDilationBridge.lean :: score=6 :: concepts=anomaly, moore_penrose, projector, conformal, dilation, chiral

## Arango SCC seed summaries
- seed1: scc_id=4377 downstream=201 upstream=30
- seed2: scc_id=12848 downstream=158 upstream=1
- seed3: scc_id=14615 downstream=532 upstream=4

## Next theorem packet skeleton
- DrazinMPProjectorCommutator
- ProjectorMismatchAnomaly
- DilationFromProjectorNoncommutativity
- ConformalClosureWitness
- Cl44ConformalReadout

Rule: Arango connectedness is navigation/audit; descend to raw Lean owners and encode explicit witness contexts.