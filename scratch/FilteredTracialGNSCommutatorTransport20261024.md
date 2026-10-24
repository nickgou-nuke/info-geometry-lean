# Native tracial GNS bonding of commutators

Candidate: FilteredTracialGNSCommutatorTransport20261024.lean. Uncompiled source.
Imports existing FilteredGNSRepresentation and promoted TracialGNSCommutator.

Generic inputs are the existing continuous star-inductive system and its
compatible native State family, a bond hij, trace cyclicity at its two ends,
and actual Hamiltonians H and K. No Hermiticity or faithfulness is needed for
transport. There is no new GNS carrier and no assumed GNS intertwining field.

Two equivalent-use entry points are provided:
- commutator_transport takes the algebraic identity
  [K,sys.map hij a] = sys.map hij [H,a] for every a, and proves
  D_K.comp filteredGNSMapCLM = filteredGNSMapCLM.comp D_H.
- commutator_transport_of_centralizing_increment derives that algebraic input
  from Commute (K-sys.map hij H) (sys.map hij a) for every old observable a.
  The centralization-to-commutator helper is elementary algebra, not a claim
  that arbitrary interactions satisfy centralization.

Proof: commutator_transport_toPreGNS combines actual filteredGNSMap_toPreGNS
and accepted tracialCommutatorGNS_toPreGNS. Continuous maps agree on all native
PreGNS representatives, so completion density proves equality on the same
completed stage spaces. PreGNS representative surjectivity is used only inside
the dense subset; no claim every completed vector has a finite representative.

Concrete integration is deliberately separate: the parent's
GrowingOnsiteCommutatorTransport20261024.lean supplies the all-index raw
onsite_commutator_concreteMap identity. Transport that identity through native
CStarMatrix equivalences, use native trace cyclicity and cstarMatrixTraceStateFamily,
then apply commutator_transport for each hij. This candidate does not duplicate
that Nat.le induction or assert a completed global compatible family yet.

No norm bound or summability premise is needed here. Those belong to the
separate accepted/pending norm layer and later uniform-family assembly.
No builds/tests/live-owner edits. Staged for independent AA and serialized QA.
