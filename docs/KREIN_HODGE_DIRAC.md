# Krein-metric Dirac adjunction

## Mathematical scope

`lean/InfoGeometry/HodgeCohomology/KreinHodgeDirac.lean` works with a native
`LinearMap.BilinForm ℝ Space` and native `LinearMap.IsAdjointPair`. It has
**no `InnerProductSpace`, norm, completeness, or positivity typeclass assumptions**.
The form is supplied explicitly. Nondegeneracy and symmetry are requested only
by the theorems that need them. This is the algebraic real Krein layer, not a
construction of an analytic Krein space or an unbounded Dirac operator.

For an indefinite form `B` and a fundamental symmetry `J`, the positive
reference form is `B_J(x,y) = B(x,Jy)`. The theorem
`adjoint_relative_to_symmetry` proves that a reference adjoint `A*` yields
the **Krein adjoint** `A♯ = J A* J`. It does not replace `B` by `B_J`.
This transport identity only needs `J² = 1`; positivity of `B_J` is not
needed for that identity. The tests supply a genuine fundamental symmetry
with symmetric nondegenerate indefinite `B` and positive-definite `B_J`.

The existing analytic owner `InfoGeometry.Krein.KreinSpace` uses an auxiliary
Hilbert product to construct this same type of indefinite adjoint. Its
reference product is not the physical indefinite pairing. The existing
`RealDoubledChiralKreinAdjoint` owner separately uses the cross-sheet Witt
metric; its adjoint must not be confused with the diagonal-metric adjoint.

## Proven dependency order

* Nondegenerate pairing + adjunction + `d² = 0` imply `(d♯)² = 0`.
* These nilpotencies imply `(d + d♯)² = d d♯ + d♯ d`.
* Symmetric pairing + adjunction imply Krein self-adjointness of `d + d♯`.
* Krein self-adjointness gives `B(D²x,x) = B(Dx,Dx)`.
* `D²x = 0` therefore gives an **isotropic image**, not necessarily `Dx = 0`.
* Kernel equality follows with the explicit extra hypothesis that the image
  has no nonzero isotropic vectors. Alternatively it follows when `D`
  commutes with `J` and `B(x,Jx)` is positive for nonzero `x`.

The Laplacian is the **square of** the Dirac operator, not its square root.
The energy identity uses a signed quadratic form, not a squared norm.

## Integration with the bounded operator owner

`KreinHodgeDiracBounded.lean` uses the existing `KreinSpace.kreinBilin`,
`KreinSpace.kreinAdjoint`, and `KreinSpace.jCLM`, with the named
`[metric : KreinSpace Space]` parameter. It proves that the existing form is
nondegenerate and that a supplied adjoint-pair relation uniquely identifies
the existing Krein adjoint. It then derives the nilpotent codifferential,
Dirac square, signed energy, and the kernel theorem conditional on commuting
with the metric symmetry. No second Krein adjoint or fundamental symmetry
is defined.

The auxiliary positive inner product in that analytic owner's typeclasses
provides its norm and continuous adjoint infrastructure. The new bounded
energy statements still use `kreinInner`, never silently substitute that
positive inner product for the indefinite pairing.

## Regression counterexample

`KreinHodgeDiracTests.lean` constructs, on `ℝ × ℝ`,

```text
B(x,y) = x₁y₂ + x₂y₁
J(x₁,x₂) = (x₂,x₁)
N(x₁,x₂) = (x₂,0).
```

It proves nondegeneracy, both signs of `B`, and
`B(x,Jx) = x₁² + x₂² > 0` for nonzero `x`. The operator `N` is
Krein-self-adjoint, is not self-adjoint for the positive reference form,
and satisfies `N² = 0` with `N(0,1) ≠ 0`. Thus its square and itself
have different kernels. Setting `d = d♯ = N` also supplies a counterexample
within the nilpotent Hodge-pair construction, not merely for an unrelated
operator.

## Native homology obstruction

`KreinHodgeObstruction.lean` instantiates the existing doubled Krein carrier
with its diagonal metric `B(x,y) = x₁y₁ - x₂y₂` and the bounded operator

```text
N(x₁,x₂) = (x₁ + x₂, -(x₁ + x₂)).
```

It proves `N♯ = N`, `N² = 0`, and `range N = ker N`. The latter constructs
an **exact native `ShortComplex (ModuleCat ℝ)`** with both arrows `N`, and
Mathlib's homology API proves `Limits.IsZero nullComplex.homology`.
Nevertheless `(1,-1)` is a nonzero exact, closed, coclosed harmonic state
for the pair `d = d♯ = N`.

Thus even **nonzero** harmonicity does not imply a nonzero homology class
in the indefinite model. This directly tests the missing positivity in
the proposed Hodge-representative argument, rather than assuming that
positive Hodge theory extends to Krein metrics.

## Modular mirror versus fundamental symmetry

A fundamental symmetry and a modular conjugation are separate data. In
complex Tomita theory the modular conjugation is conjugate-linear; it is
not automatically the complex-linear metric involution. In the repository's
real doubled representation, `modular_j` and `spectral_epsilon` are separately
defined operators. Their compatibility requires actual operator identities.

`anti_isometry_transports_adjunction` proves that conjugating an adjoint pair
by a supplied involutive anti-isometry preserves the adjoint relation. The
tests instantiate this with `(x₁,x₂) ↦ (x₁,-x₂)` for the cross-pairing above.
This is an algebraic mirror-transport theorem, not a proof of Tomita's
modular theorem or a construction of its cyclic separating state.

## Positive comparison and verification

The subsequent [Green-projector construction](KREIN_GREEN_DECOMPOSITION.md)
derives the existing Hodge decomposition packet from a Drazin inverse and
proves finite-dimensional existence of its generalized zero sector. Signed
energy uses Krein adjunction; generalized harmonicity is not silently replaced
by the positive Hodge theorem.

`HodgeDirac.lean` and `FiniteHarmonicRepresentative.lean` are explicitly
positive-inner-product comparison modules. Their norm and harmonic
representative theorems must **not** be applied to the indefinite pairing.

The Krein owners and regression modules pass isolated Lean **4.28.x** checks
against the cached Mathlib revision `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
The thirteen algebraic and fourteen bounded/homology regression axiom audits
contain only `propext`, `Classical.choice`,
and `Quot.sound`, with no `sorryAx` or added axioms.

This is **not** a verified pinned Lean 4.28.1 build. The installed 4.28.1
compiler rejects the cached 4.28.x `.olean` headers. Dependency pins have
not been changed; a compatible pinned dependency build remains necessary.
