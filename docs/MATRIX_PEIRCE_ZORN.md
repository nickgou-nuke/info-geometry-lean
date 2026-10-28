# Matrix Peirce geometry and exact Zorn defects

The import entry point is `InfoGeometry.Canonical.MatrixPeirceZorn`. Its eleven
modules formalize arbitrary complex square matrices, their algebraic Peirce
geometry, and an explicitly named matrix-valued Zorn bilinear operation.

## Theorem contract

The coefficient algebra is `Matrix n n ℂ`, for an arbitrary finite index type
with decidable equality. Ordinary matrix multiplication retains its native
associative meaning. Operator triples use `Fin 3 → Matrix n n ℂ`; the Zorn
carrier uses the native product of two matrices and two such triples. The
Zorn operation is the named function `Zorn.mul`, not the product type's
pointwise multiplication. No associative instance is asserted for `Zorn.mul`.

For an arbitrary idempotent `p`, the matrix modules prove four-corner
reconstruction and uniqueness, and identify the algebraic tangent space
`{X | p * X + X * p = X}` with the range of the odd projection. The tangent
space and even space are complementary native complex submodules. Every
tangent vector has an explicit commutator generator; for Hermitian `p`, a
Hermitian tangent vector has a skew-Hermitian generator.

For the Zorn operation, the modules prove ordered contraction/cross identities,
the full channel multiplication rules, associators, the exact grading and
exchange defects, and reflected associator cancellations. The image of the
triple-upper associator is exactly the native submodule of pairs
`Zorn.corner (-A) A`, with arbitrary matrix `A`. Products of three explicitly
chosen pairs generate any element of either opposite odd channel additively.
These range statements do not assert that each individual defect is nonzero.

`DefectCalculus` proves the Teichmüller and alternating-associator identities
for native additive bilinear maps, then specializes to ordinary matrix
composition and its doubled Jordan product. `DependencyPoset` records the
chosen prerequisites and proves that reachability is a partial order using
a strictly increasing edge rank.

`MatrixReassociation` uses native `FreeMagma` expressions with matrix-valued
leaves. A context contains exactly one hole and acts by a native
`AddMonoidHom` on its value. Each directed rotation has a correction equal
to its contextual associator. Along any finite sequence of rotations these
corrections sum to the difference of the endpoint evaluations, and two paths
with the same endpoints have the same total correction. Signed exchange
commutes with evaluation of every expression. The reflected three-channel
identity remains valid inside every context.

`MatrixReassociationOrder` supplies a separate, named native `PartialOrder`
on these actual expressions. Its order is reachability by right rotations,
not a numbering of the expressions. A strictly decreasing tree weight proves
antisymmetry, while the native `FreeMagma.toFreeSemigroup` map proves that
rotations preserve the ordered word of matrix-valued leaves. This order is
distinct from the chosen 25-archetype prerequisite order in `DependencyPoset`.

## Exact mixed-associator signs

Write `U = Zorn.upper`, `L = Zorn.lower`, `alpha = Zorn.associator`,
`t = Zorn.cross u v`, and `B(p,q) = cross p q + cross q p`. The exact identities are

```text
alpha (L w) (U u) (U v) + alpha (U u) (U v) (L w)
  = U (cross w t - cross t w)
alpha (L w) (U u) (U v) - alpha (U u) (U v) (L w)
  = U (B(w,t))
```

Replacing the first right-hand side by `U (B(w,-t))` leaves the residual
`2 • U (cross w t)`. The proposed equality therefore holds exactly when
`cross w t = 0`. This is a proved equivalence over complex matrices.

For unrestricted matrices `A`, `B`, and `C`, take the operator triples
`u = ![A,0,0]`, `v = ![0,B,0]`, and `w = ![0,C,0]`. The sum is
`U ![C*(A*B) + (A*B)*C,0,0]`; the difference is
`U ![C*(A*B) - (A*B)*C,0,0]`. The difference is nonzero exactly when
`C` and `A*B` do not commute. The incorrect signed-defect equation holds
exactly when `C*(A*B) = 0`. These results impose no scalar or diagonal
restriction on the matrix coefficients.

## Modules

| Module | Principal content |
| --- | --- |
| `DependencyPoset` | Reachability partial order, acyclicity, incomparable branches |
| `MatrixPeirce` | Arbitrary-idempotent corners, grading, adjoints, trace |
| `MatrixGeometry` | Native tangent submodule, complementary projections, commutator generators |
| `DefectCalculus` | Universal bilinear identities and matrix Jordan specialization |
| `MatrixZorn` | Matrix-valued product, Peirce extraction, corrected channel identities |
| `MatrixReflection` | Signed exchange automorphism, unsigned exchange defect, cancellations |
| `MatrixZornGrading` | Number-grading defect, additive generation, coefficient commutation criterion |
| `MatrixZornCorners` | Exact triple-associator image and opposite-corner Jacobiator |
| `MatrixBraidingDefect` | Mixed sum/difference signs, exact residual, matrix noncommutation criterion |
| `MatrixReassociation` | Native expression trees, contextual defects, finite-path corrections |
| `MatrixReassociationOrder` | Directed-rotation partial order and ordered leaf-word preservation |

## Relationship to existing owners

The existing `IdempotentOrbitContracts` owner proves generic-ring statements
`tangent_diagonal_zero`, `tangent_split`, and `tangent_horizontal_lift`.
This package includes a self-contained matrix formulation and native
`Submodule`, `LinearMap.IsProj`, `IsCompl`, and `LinearEquiv` constructions.

The existing `OperatorZornFourPotentialGauge` owner defines its associator
and bracket on `OperatorZornMatrix A`, and `OperatorZornMatrixPeirce` proves
coefficient-sector reconstruction on that carrier. This package uses a
native product/Pi carrier with its own namespaced, explicitly named product.
It does not replace those owners or claim an unproved equivalence of carriers.

The scope is finite-dimensional operator algebra and algebraic tangent
geometry. Smooth manifold charts, analytic differentiation, categorical
coherence, and Hochschild cohomology are not conclusions of these modules.
The expression results concern parenthesized products and exact evaluation
corrections. They do not identify nonassociative multiplication with category
composition or assert a logical normalization theorem.

## Integration and verification

The canonical publication umbrella imports this package. The existing
`InfoGeometryTestSuite` registers `MatrixPeirceZornAxiomAudit`.
The repository toolchain and dependency pins are reused unchanged:

- Lean `4.34.1`.
- mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

In a provisioned repository checkout, run:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock --wfail InfoGeometry.Canonical.MatrixPeirceZorn MatrixPeirceZornAxiomAudit
```

The audit collects transitive axiom dependencies for every public and private
declaration in the package. It rejects an empty selection and any dependency
outside `propext`, `Classical.choice`, and `Quot.sound`.
