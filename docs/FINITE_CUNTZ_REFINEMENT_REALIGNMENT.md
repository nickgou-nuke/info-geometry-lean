# Unique rectangular refinement instead of finite square Cuntz generators

The existing finite-stage obstructions rule out two Cuntz isometries in a
nonzero finite square-matrix algebra. Their constructive replacement already
exists in `Canonical/FiniteCantorCuntzBranches.lean`: rectangular linear maps
from `Stage n` to `Stage (n+1)`, with branch adjoints and a range partition.
`Canonical/FiniteCantorBranchAmplification.lean` defines the induced operator
refinement `amplify n T`, proves it unital, additive, multiplicative, injective,
and compatible with the existing diagonal bonding map.

The new `Canonical/FiniteCantorBranchRefinement.lean` proves the precise
universal characterization on these same stages and maps:

    V = amplify n T
      iff ∀ b : Bool, V.comp (branch n b) = (branch n b).comp T.

Consequently each smaller-stage operator has exactly one larger-stage
operator with both prescribed branch actions. The proof reconstructs vectors
using the existing range partition. It introduces no substitute matrix model,
finite square Cuntz family, or alternative continuum construction.

This characterization is stronger than merely intertwining the diagonal
bonding map. That map alone describes one subspace and does not specify the
operator's action on both branch ranges.

Source discovery inspected all three finite-stage Cuntz obstruction owners,
the rectangular branch and amplification definitions, and recursive searches
for their consumers in `lean`, `lib`, `proofs`, and `scratch`. Independent
read-only discovery confirmed reuse of the existing adjoint intertwining and
partition laws. This record classifies the finite-stage claim locally; it is
not a complete classification of the repository's counterexample inventory.

Parent audit session 78627 exited zero with 3097 jobs, log
`/tmp/finite-cantor-refinement-audit.log`. All five declarations depend exactly
on `propext`, `Classical.choice`, and `Quot.sound`; zero warnings originate in
the new owner or audit. Independent semantic review passed. Independent QA
session 25323 exited zero with 3097 jobs, log
`/tmp/finite-cantor-refinement-qa.log`: five standard-three axiom reports,
zero own-source warnings, and zero strict-screen traps.
