# Dahm exterior Klein operator action: theorem contract

## Source and reconstruction provenance

Source: Rolf Dahm, *On A Unified Derivation of Internal and Relativistic
Symmetries from Projective Geometry*, bfIS 03-2025, dated 3 November 2025,
13 pages. Supplied file: `bjp_Dahm-1.pdf`.
SHA256: `75a7a5fdcc6dc2488506e9fb6484b6b5dc55563fddde2bc53e576d649e2e74d2`.
The mathematical targets are equations (4)-(6), pages 9-10, and the
four-coordinate proposal on page 11; equation (1), pages 4-5, determines a
real-form scope boundary.

Implementation base: `c143c264bc18bbf41d692be4e270b5b7f7405702`.
Lean: `v4.34.1`. Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
This is a fresh implementation after the earlier unpushed checkout was lost.
The earlier commit and acceptance receipt are not verification evidence for
this source. Every completion claim requires a new build and independent audit.

## Intent and actual carriers

The target is finite-dimensional real exterior algebra and ordered operator
composition. Use the existing `FierzKleinFoundation.Vec4 := I4 → ℝ`, the actual
Mathlib exterior square `⋀[ℝ]^2 Vec4`, the existing `Bivector4` module, and
`ExteriorPowerPluckerBridge.exteriorBivectorLinearEquiv`. Operators range over
the full noncommutative monoid `Module.End ℝ Vec4`. Real coefficients commute;
the operators need not commute. No scalar, diagonal, or commuting restriction
is imposed on the general action and covariance theorems.

Coordinate order: `(p01,p02,p03,p12,p13,p23)`.
The paper's `p31` is `-p13`. The existing Klein form is
`Q(P) = p01*p23 - p02*p13 + p03*p12`. Its polar is unnormalized:
`B(X,X) = 2*Q(X)`.

## Existing owners and the missing implication

| Owner | Existing construction reused |
|---|---|
| `Canonical/FierzKleinFoundation` | Four-vectors, Minkowski pairing, coordinate wedges, Klein polynomial |
| `Canonical/KleinBivectorLinear` | Native linear structure on the existing bivector carrier |
| `Canonical/KleinExteriorAlternating` | The coordinate wedge as an alternating map |
| `Projective/ExteriorPowerPluckerBridge` | Actual exterior/bivector linear equivalence and decomposability theorem |
| `Projective/ExteriorKleinCoordinateIncidence` | Normalized top exterior coordinate and its determinant/incidence readout |
| `Projective/ExteriorKleinNullTwistor` | Native exterior Klein quadratic form |
| `Projective/ExteriorKleinNullTwistorIncidence` | Exact polar formula |
| `Projective/KleinQuadricIncidence` | Conditional incidence-fiber transport |
| `Projective/DahmPluckerKleinCollineation` | Current coordinate compound-matrix covariance and boost formulas |

The current compound-matrix owner is not replaced. The missing construction
is the native `exteriorPower.map` action, its ordered composition law, and the
intrinsic determinant covariance needed to construct the incidence theorem's
inputs. Search and inspect actual owner declarations; names and prose are not
accepted as proof authority.

## Theorem targets

| Target | Exact hypotheses and conclusion |
|---|---|
| Native action | Conjugate `exteriorPower.map 2 A` through the existing linear equivalence; prove its wedge readout |
| Composition | `Λ²(A ∘ B) = Λ²A ∘ Λ²B`; bundle a monoid homomorphism |
| Injectivity and inverse | An injective `A` induces an injective action; a linear equivalence induces an equivalence using its actual inverse |
| Full polar covariance | For every endomorphism `A` and every pair `X,Y`, `B(Λ²A X, Λ²A Y) = det(A)*B(X,Y)` |
| Full quadratic covariance | For every `A,X`, `Q(Λ²A X) = det(A)*Q(X)` |
| Invariance/reflection | Determinant one gives exact invariance; reflection of zero assumes determinant nonzero |
| Operator witness | Shears `I+E01` and `I+E12` fail to commute; the induced commutator on `e_y ∧ e_z` has `p03 = 1` |
| Boost formula | `(t,x,y,z) ↦ (a*t+b*x,b*t+a*x,y,z)` induces `((a²-b²)p01, a*p02+b*p12, a*p03+b*p13, b*p02+a*p12, b*p03+a*p13, p23)` |
| Minkowski normalization | `a²-b²=1` implies preservation of the existing Minkowski pairing |
| Four-coordinate sector | `p02=p12=0` reduces the Klein form to `p01*p23`; the boost preserves this sector |
| Sector obstruction | `(t,x,y,z) ↦ (t,x,z,-y)` preserves the Minkowski pairing but sends `e_t∧e_z` outside the selected sector |
| Constructed incidence transport | For each four-vector linear equivalence, construct the six-coordinate equivalence, determinant multiplier, its nonvanishing, and its covariance to invoke the existing fiber theorem |

The main covariance laws allow singular maps and nondecomposable bivectors.
They do not assume either desired covariance as a structure field.

## Dependency order

1. Native exterior map and coordinate intertwining.
2. Identity and ordered composition; inverse construction.
3. Identify the normalized top exterior functional with a basis determinant.
4. Apply Mathlib's determinant-composition law to that functional.
5. Identify the polar on two simple wedges with the top wedge and extend by
   exterior-power linear-map extensionality in both variables.
6. Derive quadratic covariance from the polar diagonal identity over `ℝ`.

The shear witness uses only the action and wedge readout. The exact boost
formula uses exterior extensionality and the action; its determinant may be
read from quadratic covariance on a bivector with nonzero Klein value. The
Minkowski calculations use the actual bilinear form. Incidence transport uses
the constructed equivalence, polar covariance, and nonzero determinant.

## Boundaries

- The map `A ↦ Λ²A` is a monoid homomorphism and is quadratic in `A`; it is
  not an additive or Lie-algebra homomorphism. The separate infinitesimal
  action `u∧v ↦ Au∧v + u∧Av` is outside this extension.
- Injectivity of each induced operator is not faithfulness of the operator
  representation: the exterior-square actions of `I` and `-I` agree.
- General invertible maps give similitudes; determinant-one maps give exact
  isometries of the Klein form.
- `incidenceFiber` is the full polar kernel in the coordinate vector space.
  Its transport does not itself add an action on projectivized nonzero
  decomposable rays.
- Page 11 names four readout coordinates but explicitly leaves constraints on
  `p02,p12` unresolved. The slice `p02=p12=0` is our chosen test slice, not an
  assumption asserted by the paper. The counterexample concerns invariance
  of this slice, not every possible four-dimensional model.
- The paper's boost parameters satisfy `a=γ`, `b=-γβ`. Recovering the usual
  positive `γ` convention additionally requires `a>0`.
- The complex substitution in equation (1) changes the real slice. No real
  equivalence between the positive six-square form and the split real Klein
  form is asserted.
- SU/SO covering or real-form classification, spacetime derivation, spin,
  entanglement, and physical unification claims remain outside the proved scope.

## Acceptance and publication

Require a complete focused build, a fresh declaration/axiom audit, independent
source review, separate non-authoring acceptance, strict source screening,
staged proof gate, and exact source fingerprints. Only `propext`,
`Classical.choice`, and `Quot.sound` are allowed and must be classified.
No proof holes, custom axioms, unsafe bypasses, or vacuous certificates.

The focused project imports the unchanged canonical sources and exact Mathlib
pins. It does not certify root optional path dependencies or the root push
gate. Observe and record those failures separately.

On 2026-11-11 the user explicitly requested an upstream PR immediately because
the local checkout is temporary. Publish this source as a draft checkpoint
while the focused build continues, with incomplete validation stated plainly.
This preserves the work remotely and does not confer mathematical acceptance.
The complete acceptance requirements above remain outstanding until executed
against the final source. Record the current root-build limitation separately.
No merge is authorized.
