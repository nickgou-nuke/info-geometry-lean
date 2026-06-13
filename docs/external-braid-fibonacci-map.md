# External Braid and Fibonacci Map

> Scope: navigation only. `external_refs` is precedent material, not proof authority.

This page maps the braid/Fibonacci lane to the repo-owned Lean files that
actually decide theorem truth, and to the external reference material that is
useful for orientation.

## External precedent material

- `external_refs/afp/thys/Knot_Theory/Tangle_Moves.thy`
- `external_refs/afp/thys/Knot_Theory/Linkrel_Kauffman.thy`
- `external_refs/afp/thys/Zeckendorf/Zeckendorf.thy`

These files are useful as braid/tangle and Fibonacci-combinatorics precedent.
They do not prove any Lean claim in this repository.

## Repo-owned braid/Fibonacci owner files

- [lean/InfoGeometry/Categorical/FibonacciBraiding.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Categorical/FibonacciBraiding.lean)
- [lean/InfoGeometry/Categorical/FibonacciBraidedTowerCone.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Categorical/FibonacciBraidedTowerCone.lean)
- [lean/InfoGeometry/Categorical/FibonacciFusionCategoryData.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Categorical/FibonacciFusionCategoryData.lean)
- [lean/InfoGeometry/Categorical/FibonacciBraidDirectLimit.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Categorical/FibonacciBraidDirectLimit.lean)
- [lean/InfoGeometry/Canonical/FibonacciParafermionAtoms.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/FibonacciParafermionAtoms.lean)
- [lean/InfoGeometry/Algebra/FibonacciParafermion.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Algebra/FibonacciParafermion.lean)
- [lean/InfoGeometry/Canonical/FibonacciGrothendieckLimit.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/FibonacciGrothendieckLimit.lean)
- [lean/InfoGeometry/Canonical/BraidColimitZornBarrier.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/BraidColimitZornBarrier.lean)

## What is actually proved

- Finite Fibonacci fusion data:
  - `N_tau * N_tau = N_unit + N_tau`
  - `F² = 1` under the explicit scalar relations
  - `det F = -1`
- Finite braid readouts:
  - `B = F R F`
  - the Artin/Yang-Baxter identity is available only as an explicit finite hypothesis in the matrix owner files
- Direct-limit transport:
  - finite-stage braid identities transport through the algebraic direct limit
- Real Majorana/Weyl decomposition:
  - `F_matrix a b = a • majoranaZ + b • majoranaX`
  - `F_matrix a b = a • sl₂H + b • (sl₂E + sl₂F)`
- Order-theoretic braid support:
  - maximal successor-closed stage subsets via Zorn-style arguments

## What is still open

- a full `BraidedCategory` instance for Fibonacci fusion data
- a proof that a concrete finite braid-word action satisfies the universal braid-group relations in the categorical sense
- a global analytic or conformal-block braid theorem

## Practical use

If you want to continue the braid/Fibonacci lane honestly:

1. use the external AFP knot-theory files as precedent only;
2. keep the Lean work inside the repo-owned finite/direct-limit owner files;
3. only promote a new theorem when it compiles in the owner file and does not overstate the scope.
