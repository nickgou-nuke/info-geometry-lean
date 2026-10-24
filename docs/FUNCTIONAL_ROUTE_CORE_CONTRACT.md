# Functional routing: recurrent coordinates versus operator shells

Base inspected: `3f12c2416c1c853ae0cbd56b09aad0d0e2fd38ad`.
The existing `DeterministicDrazinBridge`, `CausalRouteDynamics`, and
`CausalCoreTrace` owners are reused, not rewritten. In particular the native
Birkhoff/complement equivalence and the causal expected-core-trace identity
already exist and are not claimed as new work here.

## New proof contract

`FunctionalRouteCore` takes a finite recurrent-coordinate embedding, a cycle
permutation, a synchronized retraction, and an eventual-entry certificate.
It derives the canonical Drazin equations, the lifted core/inverse formulas,
and core trace. It does not assume a Drazin witness in order to construct one.
It does not prove existence of the graph certificate for every finite map or
verify a Kahn implementation. For L=R_rho and J=R_embed, J L=I,
E=L J, C=L Pi_sigma J, D=L Pi_sigma_inverse J. Ambient D=C^T does not follow.

A rectangular full-rank-factorization theorem derives the four actual MP
laws from L U=I, B T=I, and self-adjointness of U L and T B. This is suitable
for a fiber-incidence factorization N^m=U B and avoids a false claim that
pseudoinverses transport through arbitrary similarities.

`FunctionalRouteObstructions` proves exact causal-route counterexamples.
For route [0,0,1,1], token entry depths have counts (1,2) while the two
compressed shell traces are (2,1); the depth-two sibling difference vanishes
in one step. The explicit zeroth shell is not a diagonal token selector.
For route [0,0,1,2], the actual nilpotent MP supports do not commute and the
squared charge is not idempotent. A constant route has N=0 despite a nonzero
nilpotent complement, and its Drazin inverse is not the ambient core transpose.

## Interpretation boundaries

A convex combination of route-wise Drazin decompositions is a representation
of the operator, not its own Drazin decomposition. Powers of attention require
independent route draws per step, not repetition of a single sampled route.
An exact value-preserving Caratheodory replacement can change route dynamics.
Rows and columns are different actions; shell vectors are signed contrasts,
not nonnegative token-coordinate masks. Rectangular routes cannot be iterated
without an additional identification or return map.

The runtime companion provided with this change separates graph entry-depth
counts from shell ranks and keeps the unpeeled residual in readout. No training
file is changed. Numerical residuals are not Lean kernel checks. The full-rank
fiber implementation and its tests are not themselves mechanized by the two
Lean modules. The candidate sources are accepted only by a successful scoped
workflow for their exact source commit; no all-green repository CI is claimed.
