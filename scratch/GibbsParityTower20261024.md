# Gibbs parity transport from an arbitrary seed

Uncompiled scratch; independent AA and locked QA required. No builds/tests,
CAS, live edits, new carrier, or state construction.

Five proposed heads in CuntzMatrixCompatibleStateNet:
gibbsDensity_rawMap; gibbsFunctional_rawMap;
gibbsFunctional_concreteStep_odd_zero; gibbsFunctional_rawMap_odd_zero;
gibbsColimitFunctional_transport_odd_zero.

The first two take i≤j, H at i, H' at j, Hermitian proofs and exactly
H'=rawMap hij H. The density uses native StarAlgHom.map_cfc. The normalized
functional proof inducts on the transition using existing concreteStep Gibbs
compatibility, with intermediate Hermiticity obtained from map_star.
No full Hamiltonian family or condition at stage zero enters finite transport.

Parity cancellation requires only Commute H Γ, Γ²=1, XΓ=-(ΓX) at the seed.
No Γ-Hermitian hypothesis, global cyclicity, or analytic KMS assertion.
The final colimit consumer assumes functional Compatible explicitly and reuses
gibbsColimitFunctional_stage. It does not construct a nonscalar global model.

Scope: MatrixStage 0 is Matrix (Fin 1) (Fin 1) ℂ, so a Hamiltonian family
propagated by concreteStep from zero remains scalar. Do not interpret that
family as a nontrivial Gibbs example. Any seed stage i≥1 is allowed here.

Reuse navigation: CuntzTowerUpperTailActionColimit has UpperNatIndex and a
restricted TopCat diagram; FilteredGNSCofinalTail has tailHilbertGlobalEquiv
but assumes an existing compatible state family. Neither constructs the
desired nonscalar Gibbs seed. AlgebraicKMSStateColimitReadback already has
normalizedDeltaWeightedFunctional_stage_eq_gibbsFunctional for a seed unit
embedded into the existing colimit. Kepler owns its later-stage readback and
positivity extension. These rawMap lemmas complement that work; no parallel
tail carrier or duplicate arbitrary-seed state is introduced.
