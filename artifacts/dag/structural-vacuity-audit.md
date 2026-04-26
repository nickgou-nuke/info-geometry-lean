# Structural Vacuity Audit

Status: `findings`

## Summary

- Total findings: 9
- Admitted by `sorryAx`: 9
- Dependency-free local theorems: 0
- Only ignored/foundational dependencies: 0
- Arango warnings: 0

## Findings

### `InfoGeometry.Algebra.WeylDenominator.weyl_denominator_expansion`

- Classification: `admitted_by_sorry`
- Dependency count: 46
- Dependencies: NormedAddCommGroup.toENormedAddCommMonoid, instHMul, Semiring.toMonoidWithZero, Complex.instSemiring, MonoidWithZero.toMonoid, Neg.neg, Finset.sum, Complex.instNeg, Complex.instOne, InfoGeometry.Algebra.PrimeA1RootSystem, ENormedAddCommMonoid.toESeminormedAddCommMonoid, Eq, UniformSpace.toTopologicalSpace, Bool.false, OfNat.ofNat, InfoGeometry.Algebra.WeylDenominator.finiteWeylDenominator, CommRing.toCommMonoid, Complex, NormedField.toNormedCommRing, SeminormedRing.toPseudoMetricSpace, ESeminormedAddCommMonoid.toAddCommMonoid, instHPow, Finset.powerset, Lean.Name, One.toOfNat1, InfoGeometry.Thermodynamics.souriauEvaluation, Finset.card, SeminormedCommRing.toSeminormedRing, InfoGeometry.Algebra.PrimeA1RootSystem.P, Nat, HPow.hPow, Lean.Name.anonymous, Finset.prod, Lean.Name.str, Lean.Name.num, instOfNatNat, Monoid.toNatPow, sorryAx, Complex.instMul, PseudoMetricSpace.toUniformSpace, Complex.instNormedField, Finset, Complex.commRing, Complex.instNormedAddCommGroup, HMul.hMul, NormedCommRing.toSeminormedCommRing

### `InfoGeometry.Analytic.emergent_volume_is_analytic_torsion`

- Classification: `admitted_by_sorry`
- Dependency count: 11
- Dependencies: InfoGeometry.Analytic.EmergentVolumeWitness.volumeMatches, Bool.false, OfNat.ofNat, Lean.Name, Nat, InfoGeometry.Analytic.EmergentVolumeWitness, Lean.Name.anonymous, Lean.Name.str, Lean.Name.num, instOfNatNat, sorryAx

### `InfoGeometry.Arithmetic.weyl_sign_eq_moebius`

- Classification: `admitted_by_sorry`
- Dependency count: 26
- Dependencies: MulZeroClass.toZero, InfoGeometry.Algebra.PrimeA1RootSystem, DFunLike.coe, Eq, InfoGeometry.Algebra.PrimeA1RootSystem.WeylGroup, Bool.false, OfNat.ofNat, Lean.Name, ArithmeticFunction.moebius, ArithmeticFunction, NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing, Nat, Int.instCommRing, Lean.Name.anonymous, Lean.Name.str, Lean.Name.num, Int, instOfNatNat, InfoGeometry.Algebra.PrimeA1RootSystem.signature, NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring, InfoGeometry.Arithmetic.weylToNat, sorryAx, NonUnitalNonAssocSemiring.toMulZeroClass, ArithmeticFunction.instFunLikeNat, CommRing.toNonUnitalCommRing, NonUnitalCommRing.toNonUnitalNonAssocCommRing

### `InfoGeometry.Arithmetic.weyl_toNat_squarefree`

- Classification: `admitted_by_sorry`
- Dependency count: 14
- Dependencies: InfoGeometry.Algebra.PrimeA1RootSystem, InfoGeometry.Algebra.PrimeA1RootSystem.WeylGroup, Bool.false, OfNat.ofNat, Squarefree, Lean.Name, Nat, Lean.Name.anonymous, Lean.Name.str, Lean.Name.num, instOfNatNat, InfoGeometry.Arithmetic.weylToNat, sorryAx, Nat.instMonoid

### `InfoGeometry.Canonical.MeasureScaleShape.generalizedKL_scale_shape_split`

- Classification: `admitted_by_sorry`
- Dependency count: 52
- Dependencies: Set, instHMul, MeasureTheory.Measure.instFunLike, InformationTheory.klDiv, DFunLike.coe, Eq, UniformSpace.toTopologicalSpace, MeasureTheory.FiniteMeasure.normalize, Bool.false, OfNat.ofNat, SeminormedCommRing.toNonUnitalSeminormedCommRing, MeasureTheory.ProbabilityMeasure.toMeasure, Real.pseudoMetricSpace, Zero.toOfNat0, Lean.Name, Nonempty, NonUnitalSeminormedRing.toSeminormedAddCommGroup, ENNReal, MeasureTheory.IsFiniteMeasure, Real.instMul, Nat, NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing, HAdd.hAdd, Real.normedCommRing, ENNReal.toReal, instHAdd, SeminormedAddCommGroup.toSeminormedAddGroup, MeasurableSpace, Lean.Name.anonymous, InfoGeometry.Canonical.MeasureScaleShape.generalizedKL, Real.instAdd, Subtype.mk, Lean.Name.str, MeasureTheory.Measure.instZero, Lean.Name.num, instOfNatNat, Ne, MeasureTheory.ProbabilityMeasure, SeminormedAddGroup.toContinuousENorm, inferInstance, MeasureTheory.Measure.AbsolutelyContinuous, sorryAx, MeasureTheory.llr, MeasureTheory.Integrable, PseudoMetricSpace.toUniformSpace, Set.univ, InfoGeometry.Canonical.MeasureScaleShape.scalarGKL, HMul.hMul, MeasureTheory.Measure, Real, NormedCommRing.toSeminormedCommRing, MeasureTheory.FiniteMeasure

### `InfoGeometry.Canonical.ProjectiveCCR.ProjectiveBoundaryPacket.projective_boundary_packet`

- Classification: `admitted_by_sorry`
- Dependency count: 56
- Dependencies: NormedAddCommGroup.toENormedAddCommMonoid, NormedAddCommGroup, InfoGeometry.Canonical.ProjectiveCCR.ProjectiveBoundaryPacket, Complex.instOne, InnerProductSpace, ENormedAddCommMonoid.toESeminormedAddCommMonoid, Eq, Semiring.toNonAssocSemiring, UniformSpace.toTopologicalSpace, RingHom.id, NormedAddCommGroup.toSeminormedAddCommGroup, OfNat.ofNat, Complex, ESeminormedAddCommMonoid.toAddCommMonoid, Complex.instSub, Real.normedField, Lean.Name, One.toOfNat1, Function.const, And.intro, Nat, InfoGeometry.Canonical.SuperKMS_Equilibrium.SuperKMSEquilibriumState.absorption, HAdd.hAdd, SeminormedAddCommGroup.toPseudoMetricSpace, instHSub, InfoGeometry.Canonical.ProjectiveCCR.ProjectiveBoundaryPacket.regulatedHeatKernel_eq_subtract_one, Unit, And, instHAdd, Bool.true, ContinuousLinearMap, Lean.Name.anonymous, Real.instAdd, Lean.Name.str, InfoGeometry.Canonical.ProjectiveCCR.ProjectiveBoundaryPacket.split, Lean.Name.num, instOfNatNat, InfoGeometry.Canonical.SuperKMS_Equilibrium.SuperKMSEquilibriumState.stimulatedEmission, Real.semiring, sorryAx, InfoGeometry.Canonical.ChiralNullSpaceBridge.ZeroModeSubtractionWitness.regulatedHeatKernel, InfoGeometry.Canonical.ProjectiveCCR.ProjectiveBoundaryPacket.superKMS_detailed_balance, PseudoMetricSpace.toUniformSpace, HSub.hSub, InfoGeometry.Canonical.ProjectiveCCR.ProjectiveBoundaryPacket.vacuumMode_eq_one, NormedSpace.toModule, InfoGeometry.Canonical.SuperKMS_Equilibrium.SuperKMSEquilibriumState.spontaneousEmission, Real.instRCLike, InfoGeometry.Canonical.ChiralNullSpaceBridge.DrazinChiralSplitPacket.zeroMode, InfoGeometry.Canonical.ProjectiveCCR.ProjectiveBoundaryPacket.kms, InfoGeometry.Canonical.ChiralNullSpaceBridge.ZeroModeSubtractionWitness.vacuumMode, CompleteSpace, Real, InnerProductSpace.toNormedSpace, Unit.unit, InfoGeometry.Canonical.ChiralNullSpaceBridge.ZeroModeSubtractionWitness.heatKernel

### `InfoGeometry.Canonical.ProjectiveCCR.ProjectiveBoundaryPacket.regulatedHeatKernel_eq_subtract_one`

- Classification: `admitted_by_sorry`
- Dependency count: 44
- Dependencies: NormedAddCommGroup.toENormedAddCommMonoid, NormedAddCommGroup, InfoGeometry.Canonical.ProjectiveCCR.ProjectiveBoundaryPacket, InnerProductSpace, ENormedAddCommMonoid.toESeminormedAddCommMonoid, Eq, Semiring.toNonAssocSemiring, UniformSpace.toTopologicalSpace, RingHom.id, NormedAddCommGroup.toSeminormedAddCommGroup, OfNat.ofNat, Complex, ESeminormedAddCommMonoid.toAddCommMonoid, Complex.instSub, Real.normedField, Lean.Name, Function.const, Nat, SeminormedAddCommGroup.toPseudoMetricSpace, instHSub, Unit, Bool.true, ContinuousLinearMap, Lean.Name.anonymous, Lean.Name.str, InfoGeometry.Canonical.ProjectiveCCR.ProjectiveBoundaryPacket.split, Lean.Name.num, instOfNatNat, id, Real.semiring, InfoGeometry.Canonical.ChiralNullSpaceBridge.regulatedHeatKernel_eq_subtract_one, sorryAx, InfoGeometry.Canonical.ChiralNullSpaceBridge.ZeroModeSubtractionWitness.regulatedHeatKernel, PseudoMetricSpace.toUniformSpace, HSub.hSub, NormedSpace.toModule, Real.instRCLike, InfoGeometry.Canonical.ChiralNullSpaceBridge.DrazinChiralSplitPacket.zeroMode, InfoGeometry.Canonical.ChiralNullSpaceBridge.ZeroModeSubtractionWitness.vacuumMode, CompleteSpace, Real, InnerProductSpace.toNormedSpace, Unit.unit, InfoGeometry.Canonical.ChiralNullSpaceBridge.ZeroModeSubtractionWitness.heatKernel

### `InfoGeometry.Canonical.ProjectiveCCR.ProjectiveBoundaryPacket.superKMS_detailed_balance`

- Classification: `admitted_by_sorry`
- Dependency count: 41
- Dependencies: NormedAddCommGroup.toENormedAddCommMonoid, NormedAddCommGroup, InfoGeometry.Canonical.ProjectiveCCR.ProjectiveBoundaryPacket, InnerProductSpace, ENormedAddCommMonoid.toESeminormedAddCommMonoid, Semiring.toNonAssocSemiring, UniformSpace.toTopologicalSpace, RingHom.id, NormedAddCommGroup.toSeminormedAddCommGroup, OfNat.ofNat, ESeminormedAddCommMonoid.toAddCommMonoid, Real.normedField, Lean.Name, Function.const, Nat, SeminormedAddCommGroup.toPseudoMetricSpace, Unit, Bool.true, ContinuousLinearMap, Lean.Name.anonymous, Lean.Name.str, Lean.Name.num, instOfNatNat, Real.semiring, InfoGeometry.Canonical.SuperKMS_Equilibrium.SuperKMSEquilibriumState.detailedBalance, sorryAx, PseudoMetricSpace.toUniformSpace, NormedSpace.toModule, Real.instRCLike, InfoGeometry.Canonical.ProjectiveCCR.ProjectiveBoundaryPacket.kms, CompleteSpace, Real, InnerProductSpace.toNormedSpace, Unit.unit, Eq, InfoGeometry.Canonical.SuperKMS_Equilibrium.SuperKMSEquilibriumState.absorption, HAdd.hAdd, instHAdd, Real.instAdd, InfoGeometry.Canonical.SuperKMS_Equilibrium.SuperKMSEquilibriumState.stimulatedEmission, InfoGeometry.Canonical.SuperKMS_Equilibrium.SuperKMSEquilibriumState.spontaneousEmission

### `InfoGeometry.Canonical.ProjectiveCCR.ProjectiveBoundaryPacket.vacuumMode_eq_one`

- Classification: `admitted_by_sorry`
- Dependency count: 40
- Dependencies: NormedAddCommGroup.toENormedAddCommMonoid, NormedAddCommGroup, InfoGeometry.Canonical.ProjectiveCCR.ProjectiveBoundaryPacket, InnerProductSpace, ENormedAddCommMonoid.toESeminormedAddCommMonoid, Semiring.toNonAssocSemiring, UniformSpace.toTopologicalSpace, RingHom.id, NormedAddCommGroup.toSeminormedAddCommGroup, OfNat.ofNat, InfoGeometry.Canonical.ChiralNullSpaceBridge.vacuumMode_eq_one, ESeminormedAddCommMonoid.toAddCommMonoid, Real.normedField, Lean.Name, Function.const, Nat, SeminormedAddCommGroup.toPseudoMetricSpace, Unit, Bool.true, ContinuousLinearMap, Lean.Name.anonymous, Lean.Name.str, InfoGeometry.Canonical.ProjectiveCCR.ProjectiveBoundaryPacket.split, Lean.Name.num, instOfNatNat, Real.semiring, sorryAx, PseudoMetricSpace.toUniformSpace, NormedSpace.toModule, Real.instRCLike, InfoGeometry.Canonical.ChiralNullSpaceBridge.DrazinChiralSplitPacket.zeroMode, CompleteSpace, Real, InnerProductSpace.toNormedSpace, Unit.unit, Complex.instOne, Eq, Complex, One.toOfNat1, InfoGeometry.Canonical.ChiralNullSpaceBridge.ZeroModeSubtractionWitness.vacuumMode
