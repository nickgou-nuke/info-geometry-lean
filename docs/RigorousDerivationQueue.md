# Rigorous Derivation Queue

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

Last updated: 2026-04-20 (Europe/Sofia)

This file tracks unresolved derivation obligations where closure currently
depends on assumptions rather than root-forced algebra.

Companion execution surface:
- [ClosureDebtLedger.md](ClosureDebtLedger.md)

## Target A: Clock-Axis Commutation In Winding Closure

Current dependency:
- [lean/InfoGeometry/Core/CartanPhaseAxisForcing.lean](/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Core/CartanPhaseAxisForcing.lean): `commutator_KI_mem_odd`, `eq_zero_of_mem_even_and_odd`, and `commutator_KI_eq_zero_of_dual_grade_forcing` own the abstract Cartan-grade intersection route.
- [lean/InfoGeometry/Canonical/PhaseAxisCartanSymmetricLie.lean](/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/PhaseAxisCartanSymmetricLie.lean): `phaseAxisSymmetricLieAlgebra` owns the concrete phase-axis Cartan involution `θ(A) = -KAK`; `modularGeneratorGaugePart_mem_phaseAxis_even` and `modularGeneratorScalePart_mem_phaseAxis_odd` place the gauge/source split in its Cartan grades; `scaleClockCartanForcingData` packages the scale-clock forcing certificate.
- [lean/InfoGeometry/Canonical/WindingOrbitClosure.lean](/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/WindingOrbitClosure.lean): `winding_orbit_periodicity` requires `hComm : Commute K (clockAxis H)`; `modularTransportGenerator_commutator_clockAxis_eq_zero_of_cartanDualGrade` consumes explicit Cartan data to prove the concrete transport commutator vanishes; `modularTransportGenerator_commutes_clockAxis_of_cartanDualGrade` converts that result to the `Commute` witness; `winding_orbit_periodicity_of_cartanDualGrade` feeds the witness into the periodicity theorem; `modularTransportGenerator_clockAxis_commutator_eq_cartanScaleSource` identifies the commutator source as the Cartan-odd scale sector.

Gap:
- the zero-forcing step is now theorem-backed, but broad closure lanes still
  need an explicit Cartan certificate/even-membership witness or a concrete
  detailed-equilibrium certificate. The project should not hide this behind the
  old phase-linearity predicate.

Required derivation path:
1. For each target closure lane, use `scaleClockCartanForcingData` when the
   source is the modular scale sector, or construct/carry the corresponding
   `CartanPhaseAxisForcingData EndH` if a different generator is intended.
2. Prove the scale-clock/source commutator belongs to the even sector, or prove
   `modularGeneratorScalePart = 0` when detailed equilibrium is intended.
3. Route periodicity through `winding_orbit_periodicity_of_cartanDualGrade` or
   `winding_orbit_periodicity_of_detailedEquilibrium`, not through raw `hComm`.

Status: `reduced; concrete phase-axis Cartan owner and dual-grade periodicity landed`.

## Target B: Drazin/Weyl Compatibility For Inverse Lane

Context:
- Weyl compatibility is formalized in
  [lean/InfoGeometry/Quantum/TriadicWeylBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Quantum/TriadicWeylBridge.lean).
- Constructive Riesz/Drazin interfaces are in
  [lean/InfoGeometry/Canonical/DrazinInfiniteCore.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/DrazinInfiniteCore.lean).

Gap:
- the local-symmetry route now proves that an ε-symmetric constructive Riesz
  problem with regular-inverse uniqueness forces the extracted Drazin candidate
  to commute with the sheet involution, and exposes
  `constructiveRieszWeylData_of_localWeylSymmetry` for downstream consumers.
  Remaining work is to replace direct `ConstructiveRieszWeylData` assumptions
  in concrete corridors with this local-symmetry constructor when the source
  data is available.

Required derivation path:
1. State a theorem target connecting Drazin witness commutation to Weyl
   compatibility of the inverse candidate.
2. Route through the Riesz/Drazin witness package (`RieszDrazinData` or
   constructive candidate lane) rather than ad hoc choice.
3. Export the theorem into the Triadic/Weyl translator lane.

Status: `reduced; local Weyl-symmetry constructor landed`.

## Target C: Sinkhorn RN Profile Lift Equality

Current dependency:
- [lean/InfoGeometry/LLM/SinkhornDefectFlow.lean](/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/LLM/SinkhornDefectFlow.lean): `RowRNBarrierCountProfileLift` and `ColRNBarrierCountProfileLift` carry equality fields identifying raw RN barriers with scaled projective `informationGeometricRelativeNorm` readouts.
- [lean/InfoGeometry/Canonical/SinkhornGaugeThermodynamicsBridge.lean](/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/SinkhornGaugeThermodynamicsBridge.lean): Sinkhorn row/column normalization is recorded as diagonal Weyl-gauge transport, with RN force monotonicity and KMS budget consumption.
- [lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean](/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean): `countRay`, `countMassShift`, and projective count modular profile lemmas expose the count-to-projective bridge.

Gap:
- the row/column profile-lift equalities are now derived when the positive
  observed count profile has total carrier mass `n`. The trajectory-level
  construction must either prove that the relevant Sinkhorn phase supplies this
  mass certificate or carry it explicitly.

Required derivation path:
1. Route row-phase trajectories through
   `RowRNBarrierCountProfileLift.ofMassNormalized` by proving or supplying
   `countMass (rowSumCounts n M) hrow = n`.
2. Route column-phase trajectories through
   `ColRNBarrierCountProfileLift.ofMassNormalized` by proving or supplying
   `countMass (colSumCounts n M) hcol = n`.
3. Account for the projective normalization scale explicitly. Do not identify
   `trajectoryRNBarrier` with RMS `relativeInformationNorm`; the source-native
   lane is scaled `informationGeometricRelativeNorm`.

Status: `reduced; mass-normalized equality constructors and finite gauge-thermodynamics bridge landed`.

## Target D: Grand-Canonical Gauge Potential Bridge

Current dependency:
- [lean/InfoGeometry/GrandCanonical/Core.lean](/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/GrandCanonical/Core.lean): `shiftedEnergy`, `partitionGC`, `potentialGC`, `meanNumber`, `meanShift`, and the derivative laws `potentialGC_deriv_mu_eq_beta_meanNumber` and `potentialGC_deriv_beta_eq_neg_meanShift`.
- [lean/InfoGeometry/Canonical/GrandCanonicalGaugePotentialBridge.lean](/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/GrandCanonicalGaugePotentialBridge.lean): packages `μ` as a finite background gauge coupling to the count observable and re-exports the conjugate `log Z` readouts.
- [lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean](/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean): owns `bogoliubovNumberOperator` and `grandCanonicalFockGenerator`.
- [lean/InfoGeometry/Canonical/GrandCanonicalFockNumberBridge.lean](/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/GrandCanonicalFockNumberBridge.lean): packages the Fock-side `μN_B` gauge coupling and the affine generator identity.

Gap:
- the finite scalar lane and same-form Fock number coupling are closed. A theorem equating finite count profiles with Fock occupation readouts is not present and should not be assumed.

Required derivation path:
1. If needed, define an explicit occupation readout from Fock states to finite/count data.
2. Prove compatibility with `bogoliubovNumberOperator`.
3. Only then state a finite-count-to-Fock-occupation representation theorem.

Status: `finite grand-canonical lane and Fock same-form number coupling landed`.

## Target E: Chiral Light-Cone / KKT / Fock Charge Reconciliation

Current dependency:
- [lean/InfoGeometry/Canonical/OperatorSpacetimeObservables.lean](/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/OperatorSpacetimeObservables.lean): `epsilonObservable_eq_lightconePlus_sub_lightconeMinus` owns the primitive light-cone signed-polarization readout.
- [lean/InfoGeometry/Canonical/GlobalChiralDecomposition.lean](/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/GlobalChiralDecomposition.lean): `chiralRangeDomain_decomposition` owns the KKT/TKK signed chiral polarization `Γ_G = P_R - P_L`.
- [lean/InfoGeometry/Canonical/ClosureDrazinBridge.lean](/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/ClosureDrazinBridge.lean): `supercharge_eq_commutator_P_D_GammaG` and `commutator_P_D_GammaG_eq_sub_anomalies` own the Drazin supercharge/defect closure.
- [lean/InfoGeometry/Canonical/SuperchargeCARCCRBridge.lean](/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/SuperchargeCARCCRBridge.lean): primitive CAR/CCR supercharge closure.
- [lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean](/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean): `bogoliubovNumberOperator` owns the Fock occupation operator.
- [lean/InfoGeometry/Canonical/ChiralChargeFockNumberBridge.lean](/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/ChiralChargeFockNumberBridge.lean): `ChiralLightconeKKTClosure` packages these owner identities together.

Gap:
- the reconciliation package is closed, but no theorem identifies Fock
  occupation with a chiral defect, a central charge, or a finite count profile.
  Such an identification needs an explicit representation/readout theorem.

Required derivation path:
1. Define the representation/readout functor from the chiral/KKT operator lane
   to the Fock occupation lane, or from Fock states to finite observed count
   profiles.
2. Prove compatibility with `bogoliubovNumberOperator` and the Drazin
   supercharge/chiral defect readout.
3. Only then state any equality between `N_B`, chiral charges, central charges,
   or finite counts.

Status: `reconciliation package landed; representation theorem remains future work`.

## Closure Policy

- No new capstone claims should consume these assumptions without explicit
  reference to this queue.
- Preferred output is theorem-level replacement, not new prose wrappers.
