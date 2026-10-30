# Wheeler epilogue: exact algebra and bounded automation

## Intake and owner alignment

Input: the fourteen-law `WheelerEpilogue` fragment supplied in the conversation.
It proposes selective unfolding followed by distributive normalization and
`abel`, together with a claim of a universal decision procedure. Earlier
Archetypes XXXIV--XXXVI and LII are background, not additional proof premises.

The canonical module uses the existing owners:

- `Core.PeirceDecomposition`: `component10`, `component01`, and their
  square-zero corner laws.
- `Core.PeirceCoupledCorners`: `reflection_mul_jordan`.
- `OperatorAlgebra.PeirceSuperoperators.SquareZeroPair`: the ordered
  multiplication identities for square-zero pairs.
- `OperatorAlgebra.SquareZeroModeActions`: native `LieAlgebra.ad` action laws.
- `Examples.RealMatrixModeWitness`: the original dense real matrices `x,z`.

No new base algebra, scalar stand-in, diagonal carrier, or commuting-input
hypothesis is introduced. The supplied names are reproduced only in the
regression module, with ASCII spellings and a clearly separate namespace.

## Exact theorem contract

Carrier: an arbitrary associative unital ring `B`; for the countermodel,
`Cl11TensorTowerLimit.Stage 2`, the existing full real 4-by-4 matrix algebra.

Given `p*p=p`, set `u=component10 p a`, `v=component01 p c`,
`e=u+v`, `j=u-v`, `m=u*v+v*u`, and `s=[u,v]`. The canonical theorem
`InfoGeometry.WheelerEpilogue.fourteen_laws` retains all fourteen supplied
identities, with `reflection p` in place of the equal expression `p-(1-p)`.
Its linear operators are native `Module.End` values obtained from
`LieAlgebra.ad`. The weight `m` remains an operator, not a numerical eigenvalue.

`signed_endomorphism_partition` proves the last identity for three arbitrary
endomorphisms. It needs no `p`, no square-zero elements, and no division by
2 or 8. It is additive cancellation, not orthogonality or idempotence.

## Countermodel to the projector interpretation

For the existing dense witness, let
`F=-ad(x+star x)^2`, `G=ad(x-star x)^2`, `H=-ad([x,star x])^2`.
The new witness theorems establish `F z=G z=H z=-z`.
Hence `T=F-G-H` satisfies `T z=z` for the already proved nonzero matrix `z`.
The scaled-idempotence equation `T*T=8*T` fails, and the native real
endomorphism `(1/8) • T` is not idempotent.

This refutes the claimed projection interpretation without discarding
noncommutativity or replacing the matrix carrier.

## Tactic contract

The regression runs all fourteen original equations using a selectively
unfolding `simp only` list followed by `<;> abel`. The sequencing also works
when `simp` closes the goal. The list explicitly handles `neg_mul`, `mul_neg`,
`zero_mul`, and `mul_zero`; these are not inferred from the physical prose.
It checks failure and rollback of a multi-definition `unfold` containing an
absent symbol, and tests internal unary negation.

This is a tested tactic on the displayed regressions. Neither termination
and confluence of a reified rewrite system nor semantic completeness of this
Lean macro is proved. A sound proof-producing tactic can be incomplete.

## Logical order

Independent branch: additive endomorphism group -> signed partition.

Main branch: Peirce corners -> square-zero equations -> ordered quadratic
identities -> conserved operator weight -> double-commutator actions ->
fourteen-law assembly.

Countermodel branch: existing dense matrix products + right-annihilator
commutator reduction -> three actions on `z` -> failure of scaled and
normalized idempotence.

The native audit extracts actual type/value references. The committed sketch
above is an explanatory dependency order; it is not represented as an already
compiler-extracted graph. CI generates the checked graph when it succeeds.

## Verification status

This continuation is submitted to the existing draft PR for fresh verification.
The current workspace has no Lean executable and cannot resolve GitHub from its
shell; earlier local verification counts are not reused as evidence for these
new declarations. The scoped workflow checks the exact current source against
the repository's existing toolchain and Mathlib pins, audits owned declarations,
and uploads source hashes, compiler logs, and dependency data.

A passing scoped result does not certify `InfoGeometry.All` or the repository's
full root gate. Existing Atlas/GIFT dependency declarations are unchanged.
