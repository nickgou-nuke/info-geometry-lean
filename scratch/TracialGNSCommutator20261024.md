# Native tracial GNS commutator operator

Candidate: TracialGNSCommutator20261024.lean, importing promoted native
OperatorAlgebra.TracialGNSRightMultiplication. Source only, uncompiled.

For a positive linear functional f on a possibly nonunital C-star algebra,
assume primitive trace cyclicity. All operators use the SAME native f.GNS:
- rightMulMapGNS_mul: R_(a*b) = R_b.comp R_a (opposite composition).
- left_rightMulMapGNS_commute: native left action L_a commutes with R_b.
- rightMulMapGNS_star: star R_b = R_(star b), via native completed inner product,
  trace cyclicity on representatives, and two-variable completion density.
- tracialCommutatorGNS H := native gnsNonUnitalStarAlgHom H - rightMulMapGNS H.
- Representative readback is [H*a-a*H].
- IsSelfAdjoint H implies IsSelfAdjoint of this actual difference.
- Operator norm <= 2*norm H, using native nonunital star-hom contractivity
  and the proved completed right-action bound.

No faithfulness, normalization, new Hilbert carrier, or assumed adjoint/closure
conclusions. The operator is D=L_H-R_H; iD is the time generator, not the
self-adjoint operator claimed here. No assertion of cross-stage compatibility,
new tail action, or a growing Hamiltonian family is bundled into these lemmas.

No builds/tests/live-owner edits. Independent AA and serialized QA required.
