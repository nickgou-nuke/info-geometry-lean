# Concrete growing onsite trace-GNS compatible family

Frozen source candidate: GrowingOnsiteTraceGNSFamily20261024.lean.
Pending native import: InfoGeometry.Canonical.GrowingOnsiteMatrixNorm.
Other imports are the actual promoted all-index onsite transport, generic
tracial GNS transport, native filtered GNS Hilbert system, and existing
compatible-operator self-adjoint completion owner.

Input: actual weights w : Nat -> Real with Summable (fun j => |w j|).
No compatible Hamiltonian field, GNS transport field, uniform-bound assumption,
faithfulness witness, or completed-operator symmetry premise is added.

Actual stage carrier is GNSStage CStarMatrixStage cstarMatrixInductiveSystem
cstarMatrixTraceStateFamily n. The exact existing
filteredGNSIsometricDirectSystem supplies its bonding maps and Hilbert colimit.
Local E/S notation does not define a replacement carrier or direct system.

Proved construction chain:
- cstarTrace_cyclic unfolds the actual trace state and uses matrixTraceState_mul_comm.
- cstarOnsite_selfAdjoint transports raw onsite Hermiticity through the native
  Matrix-to-CStarMatrix equivalence.
- cstarOnsite_commutator_map transports onsite_commutator_concreteMap through
  that equivalence for every i<=j; it does not duplicate the raw induction.
- onsiteStageOperator is native tracialCommutatorGNS of the actual H_n.
- onsiteStageOperator_transport applies the generic proved GNS transport and
  identifies native CLM transitions with native isometric-system transitions.
- onsiteStageOperator_norm_le derives norm <= 2*sum' |w_j| from the accepted
  tracial commutator bound and the pending native onsite matrix norm theorem.
- onsiteCompatibleOperatorFamily fills op, intertwines, bound, and norm_le with
  these constructions/proofs. The bound field is the derived 2*sum' |w_j|.
- onsiteCompletedOperator uses existing completedOperator on the same native
  Hilbert colimit. Its self-adjointness follows from the proved stagewise
  property via completedOperator_selfAdjoint, and actual stage readback is given.

The family is the growing onsite recursion, not a fixed seed propagated from
stage zero. This artifact does not yet prove completed fresh-tail nonzero
readback. That remains a subsequent consumer of the raw fresh-tail theorem,
faithful matrix trace, and isometric stage inclusion; it is not assumed here.
No coupled-boundary interaction or unbounded Dirac claim is made.

Source reviewed and staged, but uncompiled. Independent AA and serialized QA
are required. No builds/tests or live-owner edits were performed.
