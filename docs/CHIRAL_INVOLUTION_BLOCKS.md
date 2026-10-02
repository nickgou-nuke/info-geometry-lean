# Chiral involutions and operator blocks

## Owner reuse

`CliffordWeyl/ChiralIdeals.lean` extends, rather than replaces, these owners:

- `OperatorAlgebra/ChiralProjectorFromInvolution.lean`: `ChiralInvolution`,
  both half-projectors, idempotence, annihilation and completeness.
- `Core/PeirceDecomposition.lean`: complementary idempotents and four-block
  reconstruction.
- `QuantumContext/MassAsCommutantCoupling.lean`: sector swapping implies
  vanishing diagonal corners; the signed grading anticommutes with a swap.
- `Algebra/IdempotentCornerCommutant.lean`: principal left and right ideals.
- `Clifford/DiracPauliGamma.lean`: concrete complex Dirac matrices, their
  chirality involution and anticommutation relations.

No new `ChiralCliffordAlgebra` class or independent projector definition is
introduced. The existing owner calls `(1 + chi)/2` `Pleft` and `(1 - chi)/2`
`Pright`; these names have the opposite sign convention to the submitted text.
The algebraic statements are independent of that naming choice.

## Dependency structure

```text
involution + real-algebra scalars
  -> complementary idempotents
     + commutation hypothesis -> diagonal blocks
     + anticommutation hypothesis -> sector swap <-> zero diagonal blocks
                                  -> off-diagonal reconstruction

two anticommuting-with-chi operators -> their product commutes with chi
```

Commutation and anticommutation are parallel hypotheses, not successive
consequences. The new bridge proves both directions of the off-diagonal
characterization, not just the forward implication from an assumed swap.

## Ideals and scope

Left multiplication by an odd operator exchanges the right ideals `Pleft A`
and `Pright A` in the indicated direction. Right multiplication exchanges the
left ideals `A Pleft` and `A Pright`. This distinction matters: every left
ideal is already preserved by arbitrary left multiplication.

These are complementary idempotents, not automatically primitive idempotents.
Their product being zero is algebraic annihilation, not a proof of Hilbert
orthogonality without an adjoint/inner-product hypothesis. No identification
of one sector with an operator commutant is made.

Anticommutation proves an operator is off-diagonal. It does not prove that
the operator vanishes, that it is physically a mass operator, or that a
positive mass or spectral gap exists. Tests include a nonzero Dirac operator,
an even product of gamma matrices, and a degenerate involution whose one
sector is zero and whose other projector admits a proper subidempotent.

## Verification

The test module imports the bridge and requests axiom reports for each new
named theorem. After checking for running compiler processes, use:

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.CliffordWeyl.ChiralIdealsTests
```

Compilation and axiom-report inspection remain pending until this command
finishes successfully. The source contains no `sorry`, `admit`, or new axiom.
No categorical infrastructure, dependency pins, or unrelated owner files
are modified.
