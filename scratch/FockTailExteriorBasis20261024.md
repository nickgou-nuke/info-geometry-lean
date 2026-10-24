# Finite Fock exterior basis transport — batch 1

Status: uncompiled sandbox candidate, not proof acceptance. No builds, tests,
live owner edits, Hilbert instances, or scalar refactor.

## Exact contract
For every n and S : Finset (Fin n), native fockTailMap n sends
(Pi.basisFun ℝ (Fin n)).ExteriorAlgebra S to
(Pi.basisFun ℝ (Fin (n+1))).ExteriorAlgebra (S.map (Fin.succEmb n)).
This includes n=0 and the empty occupancy. Both sides inhabit the existing
SpinorSpace(Vector n)=CliffordAlgebra(0) real carrier. No named replacement
basis or carrier is introduced. No naturality hypothesis is assumed.

## Source-backed proof route
- InfoGeometry/Clifford/ClNNNeutralChevalleyBridge.lean:598–645:
  vectorHeadZero uses Fin.cases 0; fockTailIsometry is zero-quadratic;
  fockTailMap is CliffordAlgebra.map of that actual map.
- Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.lean:429–445:
  ExteriorAlgebra.map is definitionally the same zero-quadratic Clifford map;
  map_apply_ιMulti proves ordered wedge naturality.
- Mathlib/LinearAlgebra/ExteriorAlgebra/Basis.lean:30–41:
  the actual basis is the graded exterior-power basis; basis_apply_ofCard
  expresses it as ιMulti_family.
- Mathlib/Order/Hom/PowersetCard.lean:38–49 identifies its increasing
  enumeration with Finset.orderEmbOfFin.
- Mathlib/Data/Finset/Sort.lean:260 proves uniqueness of increasing enumeration.
  The candidate derives the reusable order-embedding map lemma from it.
- Mathlib/Order/Fin/Basic.lean:345–349 supplies succOrderEmb and its underlying
  succEmb. Thus no reorder/sign correction is needed.

The native neutral/Fock direct-limit owners and relevant exterior-basis searches
were inspected; no equivalent all-n basis-transport declaration was found in
that bounded search. Existing fockTailMap_generator and contraction naturality
are reused infrastructure, not assumed basis transport.

## Delta and boundaries
Four separate lemmas: coordinate basis shift, increasing-enumeration transport,
native ordered wedge transport, and exterior basis transport. The wedge lemma
is a definitional specialization of native Mathlib naturality, used by the final
proof. No theorem packet, assumed metric, Hilbert isometry, adjoint relation,
norm bound, positivity, or completion claim. Later real generalization versus
explicit complexification remains undecided. Prior FockHilbertUpgrade research
and all other agent work are preserved. Parent AA/serial QA must check elaboration.
