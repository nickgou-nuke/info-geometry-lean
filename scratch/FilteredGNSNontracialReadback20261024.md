# Completed nontracial readback transport

Uncompiled source candidate. Independent AA and locked QA required. No builds,
tests, CAS or live-owner edits. Imports current native vacuum-state and finite-seed owners.

Two heads:
- FilteredGNSNontracialReadback.representedVacuumState_not_tracial transports
  an actual product-expectation inequality in a compatible stage state to the
  constructed representedVacuumState on its existing completed C⋆ closure.
- AlgebraicKMSStateColimit.finiteSeed_representedVacuumState_not_tracial takes
  H Hermitian at arbitrary matrix stage k, β real, and a,b with unequal Gibbs
  product expectations. Its conclusion is nontraciality of the represented
  vacuum State for finiteSeedCompatibleStageStates H hH β, at every choice v
  of vacuum stage. This is not merely a condition on an unrelated generic family.

The proof uses a local codomain restriction of the existing global stage
representation, its genuine multiplicativity, and representedVacuumState_stage.
The finite specialization uses Matrix→CStarMatrix.ofMatrixStarAlgEquiv and
normalizedDeltaWeightedFunctional_stage_eq_gibbsFunctional. No carrier,
global representation, state, or conclusion bundle is reconstructed.

The premise is finite scalar inequality, not assumed nontraciality of a
completion. Faithfulness of the whole representation is unnecessary: readback
forces this inequality to survive. No claim is made that every Gibbs density
is nontracial (scalar Hamiltonians in particular do not provide such a witness).
An explicit finite tilt witness can instantiate the second theorem later.
This candidate does not compute that witness or assert analytic KMS dynamics.
