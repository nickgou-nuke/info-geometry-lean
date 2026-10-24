# Actual finite-seed represented real-time evolution

Candidate: FiniteSeedRepresentedRealTime20261024.lean. Source-only, uncompiled.

Inputs are an arbitrary native finite seed stage k, Hermitian matrix H, real
beta, real time t, and a choice v of vacuum stage. No flow, state invariance,
traciality, or commutation conclusion is supplied as an input.

Native reuse and proof chain:
- seedStageHom composes the existing Matrix-to-CStarMatrix star equivalence,
  CStar algebraic direct-limit injection, and represented-closure homomorphism.
- seedHamiltonian_selfAdjoint follows from map_star and H.IsHermitian.
- seedGenerator is this actual image as a selfAdjoint element of the existing
  closure, not a new carrier or Hamiltonian witness package.
- representedDensityUnit is the same mapped seedDensityUnit as accepted
  FiniteSeedRepresentedKMS. Its value is the stage image of gibbsDensity.
- representedDensity_commutes_generator maps the native theorem
  gibbsDensity_commutes_of_commute H H hH (Commute.refl H) beta.
- seedUnitary and seedUnitaryFlow instantiate the existing
  FilteredGNSBoundedGeneratorUnitaryFlow construction. Exponential commutation
  proves representedDensity_commutes_unitary. Mathlib continuous_expUnitary
  proves time continuity.
- seedRealTimeAut is native Unitary.conjStarAlgAut. Zero, addition, and
  norm-continuous observable orbits are proved for the positive-time action
  exp(i t Hhat) A exp(-i t Hhat). The time-reversing completion adapter is not
  used or silently identified with this convention.
- twisted_readout_unitary_invariant is a generic algebraic calculation for any
  readout, a density unit, and a commuting unitary. It requires no positivity.
- representedVacuumUnitaryInvariant is a transparent proposition about the
  existing normalized positive representedVacuumState. Its abstract transport
  lemma keeps concrete spectral-order elaboration out of the specialization.
- finiteSeed_realTime_state_invariant supplies both required facts from actual
  native theorems: accepted finite-seed twisted cyclicity and the proved
  density/unitary commutation. It concludes invariance for every closure
  observable and every vacuum-stage choice.

Scope: real-time star automorphisms and invariance of the actual finite-seed
state for all real beta. This does not assert strip holomorphy, analytic KMS
boundary conditions, faithfulness, or a general unbounded-generator theorem.
No new carrier, aggregate conclusion bundle, or axioms are introduced.

QA remains with the parent's exclusive serialized lane. No build, tests, or
live-owner edits were performed. Candidate and contract are staged.
