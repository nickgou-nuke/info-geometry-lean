# Finite-seed represented twisted cyclicity — source contract

Candidate: `FiniteSeedRepresentedKMS20261024.lean`, uncompiled scratch.
Planned helper import: `InfoGeometry.OperatorAlgebra.DenseTwistedCyclicity`,
using Kepler's `twisted_cyclicity_of_denseRange` without duplicating its proof.

For every native finite Hermitian matrix H at arbitrary seed k, real beta,
and vacuum stage v, the actual constructed represented vacuum State satisfies
phi(X Y) = phi(Y (d X d^-1)) for all X,Y in its represented C-star closure.
The unit d is the homomorphic image of the actual native gibbsDensityUnit.
No completed twisted identity, traciality, or state invariance is assumed.

Construction/proof chain:
1. matrixStageReadback uses the existing CStarMatrix equivalence inverse and
   raw matrix stageInjection.
2. cstarColimitToMatrixColimit descends these maps using native liftStarAlgHom,
   cstarConcreteMap_toMatrixStage, and stageInjection_transition.
3. seedDensityUnit maps gibbsDensityUnit through the forward stage equivalence
   and native CStar algebraic injection; seedDensityUnit_readback identifies
   its reverse image with stageUnitToColimit.
4. finiteSeedVacuum_algebraic_readback is proved by direct-limit induction,
   native represented vacuum stage readback, and finiteSeedStageState_apply.
5. The existing normalizedDeltaWeightedFunctional_kms supplies the dense
   identity. Kepler's generic density theorem extends it using the actual
   representedVacuumFunctional and its continuity.
6. representedVacuumTwistedCyclic is a transparent property of the existing
   actual State, defined abstractly to avoid concrete spectral-order expansion.
   It introduces no carrier, replacement state, or certificate structure.

The density is a unit, not asserted unitary. Its conjugation is not claimed
star-preserving. This is a completed algebraic twisted product identity, not
analytic KMS strip continuation, modular-group classification, or faithfulness.
No restriction to scalar seeds or propagation from stage zero is imposed.

QA: source only. No builds/tests run. Both the planned helper import and this
candidate require serialized kernel validation before promotion claims.
