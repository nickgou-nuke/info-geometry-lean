# Klein Geometry as an Operator-Algebra Fixed-Point Theory

## Status

- Lane: Black Book bridge note
- Scope: Erlangen/Klein invariants rewritten in operator-algebra language
- Guardrail: finite-stage equivariance first, direct-limit invariance only when the bonding maps and actions are compatible

## Core claim

In this repository, a geometry is not a naked point set.
It is the invariant content of an operator algebra under a symmetry action.

If a group `G` acts on an operator algebra `X` by automorphisms, then the geometry is the fixed-point algebra

`X^G = { a ∈ X | g · a = a for all g ∈ G }`.

If the action is by conjugation through a representation `U_g`, then

`g · A = U_g A U_g^{-1}`,

and the invariants are exactly the commutant:

`X^G = { A | U_g A = A U_g for all g ∈ G }`.

That is the operator-algebra version of Klein's Erlangen program.

## Distilled invariant

The invariant is not "the group" itself.
The invariant is the algebraic structure that survives the group action:

- fixed operators,
- commuting subalgebras,
- central Casimirs,
- conjugacy-invariant spectral data such as `charpoly`,
- and equivariant decomposition data.

For Clifford-type carriers, the same principle reads:

- the quadratic form is preserved by `O(p,q)`,
- the null-cone / projective structure is preserved by the conformal readout,
- the commutant and center are the operator-level invariants.

## Repo corridor

The relevant owner and transport surfaces are:

- `lean/InfoGeometry/Clifford/ConformalLift55.lean`
- `lean/InfoGeometry/Clifford/ConformalReflection55.lean`
- `lean/InfoGeometry/Clifford/ConformalLieAlgebra55Dilation.lean`
- `lean/InfoGeometry/Clifford/DiscreteMoebiusGroup.lean`
- `lean/InfoGeometry/Clifford/ConformalProjectiveEmbedding55.lean`
- `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/JordanNormalForm.lean`
- `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/JordanChevalleyBridge.lean`
- `lean/InfoGeometry/Algebra/DirectLimitSuperClosureLemmas.lean`
- `lean/InfoGeometry/Algebra/InductiveTransportDirectLimitSUSY.lean`
- `lean/InfoGeometry/Canonical/SplitCliffordDirectLimit.lean`
- `lean/InfoGeometry/Canonical/FibonacciGrothendieckLimit.lean`

The Jordan corridor owns the finite spectral side:

- characteristic polynomial factorization,
- generalized eigenspace transport,
- torsion/PID decomposition,
- Jordan-Chevalley splitting,
- and the similarity readout for block-list Jordan matrices.

The direct-limit corridor owns the infinite tower side:

- finite-stage bonding maps,
- compatible cones,
- stagewise transport,
- colimit lifts,
- and the Grothendieck/Sugawara readout.

## Finite-stage rule

At each finite stage, invariance is clean if the bonding maps are `G`-equivariant.
Then the fixed-point data pulls forward through the tower.

That is the safe statement for the Bott / Clifford / semigroup induction lanes:

- if the stage maps commute with the symmetry action,
- then invariant operators transport stagewise,
- and the colimit inherits the action.

In that sense, `X^G` is stable under the tower only because the tower itself is equivariant.

## Direct-limit rule

The limit is not automatic magic.
If the tower is purely algebraic and the action is compatible at every stage, then the invariant structure descends cleanly to the colimit.

If the limit involves a completion, analytic closure, or current-algebra regularization, then a separate closure step is needed to preserve the invariance globally.

This matters in the repository because:

- the finite split `Cl(1,1)` atom is a local building block,
- the Bott tower stabilizes by induction,
- but the Heisenberg / Virasoro / Sugawara current lanes require a separate mode-indexed construction.

The finite atom does not by itself prove the infinite current algebra.

## O(5,5) readout

`O(5,5)` is a finite-stage symmetry of the split conformal carrier.
In the standard irreducible operator realization, the fixed-point algebra is typically just the scalars:

`X^{O(5,5)} = R · 1`.

That is the expected Klein invariant in the full orthogonal action.

More refined subgroups can preserve larger structures:

- `Spin(5,5)` can preserve orientation-sensitive data,
- `Pin(5,5)` includes reflections,
- the conformal/projective readout keeps the null-cone and incidence structure,
- the Jordan and Schur corridors preserve spectral decomposition data.

## Formal move

The safe formalization strategy is:

1. state the operator-algebra fixed-point definition,
2. state the stagewise equivariance condition,
3. state the direct-limit transport lemma as a compatibility result,
4. keep the global completed limit separate from the purely algebraic colimit,
5. treat `O(5,5)` as a finite-stage symmetry whose invariant subalgebra is the commutant / scalar fixed-point algebra in the irreducible case.

## Remaining debt

What is not proved by this note alone:

- a global analytic theorem identifying the completed infinite-limit fixed-point algebra,
- a literal derivation of the Heisenberg/Virasoro current algebra from the finite `Cl(1,1)` atom alone,
- a universal `O(infty, infty)` theorem for the tower without an explicit compatible colimit action,
- any claim stronger than the repo's actual equivariant transport lemmas.

The correct slogan is:

> Klein geometry becomes operator algebra here, and the geometry is the fixed-point structure of an equivariant symmetry action. The direct limit preserves that structure only through explicit compatibility, not by default.
