# Rotor transport into the native matrix algebraic colimit

Status: theorem contract, not kernel certification. Author: parent coordinator.

Reuse Stream 5 IsDualSeedPair and movingPolePlus/phaseRotor, Stream 3 kmsModularWeight,
and the existing CuntzMatrixAlgebraicStarColimit.Carrier and stageInjection.
No new carrier, colimit, pair class, state or completion is introduced.

Proposed deltas:
1. Ring homomorphisms preserve all four actual seed-pair equations.
2. Algebra homomorphisms commute with phaseRotor, movingPolePlus, and the squared-weight density.
3. Specialize these equalities to native stageInjection : MatrixStage n →⋆ₐ[ℂ] Carrier.
4. Native traceFunctional of a transported rotated idempotent equals the finite matrixTraceState
   of that rotated idempotent, by the existing traceFunctional_stage readback.
5. Show compatibility with the actual concreteMap transition through stageInjection_concrete_transition:
   the rotated stage observable is independent of which later stage carries it.

Owners inspected: Canonical/DeBruijnRotorAlternationCycle.lean definitions 71–108;
Canonical/UnifiedGeometryOperatorSignificance.lean weight definition;
Canonical/CuntzMatrixAlgebraicStarColimit.lean stageInjection 99, transition 139;
Canonical/CuntzMatrixAlgebraicTraceFunctional.lean traceFunctional_stage 49;
Canonical/CuntzMatrixTraceTower.lean concreteMap native AlgHom.
Search: relevant rotor/map/support and pair signatures in Canonical/Algebra/Clifford;
no matching actual Stream5-to-this-colimit transport located in that bounded search.

These are genuine homomorphism/readback statements with consumers. No generic map injectivity,
no analytic continuation, no completed C*-KMS theorem, no new dynamics or trace positivity theorem.
The native finite pair witness exists in Stream5; matrix-stage claims quantify actual matrices and
pair hypotheses, not a new structure with an uninhabited output requirement.

Verification: independent AA, then sole serial QA through shared lock, dependencies, narrow source,
all actual declarations and strict screen; parent promotion followed by native QA.
