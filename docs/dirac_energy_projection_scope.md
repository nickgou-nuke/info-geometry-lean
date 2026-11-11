# Dirac energy residuals, exterior incidence, and compression curvature

This change connects three existing native algebraic APIs. The statements below
describe their exact mathematical scope; compiler and axiom-audit results must
be reported separately for the reviewed commit.

## 1. Energy normalization and the odd residual

The generic carrier is an arbitrary associative real algebra `A`. Suppose

\[
E\ne0,\qquad H^2=E^2 1,\qquad vH+Hv=2k1.
\]

`OperatorAlgebra/EnergySignInvolution.lean` constructs the involution
`chi = E⁻¹ • H` and proves its square-one law. It also proves directly that
`(E²)⁻¹ • H` is a two-sided inverse of `H`. No division operation on the
noncommutative carrier is assumed.

For

\[
\eta=v-\frac{k}{E^2}H,
\]

the owner proves that `eta` anticommutes with both `H` and `chi`. The existing
`ChiralInvolution` carrier supplies the complementary algebraic idempotents
`Pleft = (1 + chi)/2` and `Pright = (1 - chi)/2`; its name does not identify
energy sign with the physical chirality matrix. Reusing `CliffordWeyl/ChiralIdeals`,
the new API obtains

\[
P_+\eta P_+=P_-\eta P_-=0,\qquad
\eta=P_+\eta P_-+P_-\eta P_+.
\]

If additionally `v * v = 1`, then

\[
\eta^2=\left(1-\frac{k^2}{E^2}\right)1.
\]

These hypotheses do not require `A` to be commutative, diagonal, a matrix
algebra, or a positive inner-product space. Interpreting the idempotents as
positive and negative energy spectral projections requires a suitable
self-adjoint representation and the positive choice of `E`.

### Concrete Dirac specialization

`Physics/DiracEnergyOddPart.lean` uses the existing full `DiracMatrix` carrier
`Matrix (Fin 4) (Fin 4) ℂ`, viewed as a real algebra, and the existing definitions

\[
\alpha_1=\gamma^0\gamma^1,\qquad
H=cp\alpha_1+mc^2\gamma^0.
\]

The existing dispersion theorem supplies `H²`, and the added alpha
anticommutator supplies `alpha1 * H + H * alpha1 = 2cp • 1`. A scalar-action
lemma explicitly transports the complex coefficients to the real action used
by the generic owner. For `E ≠ 0` and `E² = c²p² + m²c⁴`, the concrete residual is

\[
\eta_1=\alpha_1-\frac{cp}{E^2}H,\qquad
\eta_1^2=\frac{m^2c^4}{E^2}1.
\]

This residual is dimensionless; the velocity residual is `c` times it. The
zero-mass theorem proves `eta1 = 0` from the explicit formula `H = cp alpha1`
and the nonzero energy relation. It does not infer that a square-zero element
of a ring must vanish. That inference is false even for real matrices.

The construction is a single longitudinal momentum fiber. It does not model
unbounded position operators, a transverse family, or time-dependent states.

## 2. Exterior-square obstruction and real plane incidence

`Algebra/GrassmannianCartanTower.lean` adds the native exterior-algebra identity

\[
(u\wedge v+w\wedge z)^2=2(u\wedge v\wedge w\wedge z).
\]

It holds for any commutative coefficient ring and module, including
characteristic two. The proof uses Mathlib's alternating multilinear map,
the square-zero law for a decomposable blade, and the degree-two commutation
sign. No coordinate invariant substitutes for the exterior product.

`Projective/ExteriorKleinTwoPlaneIncidence.lean` specializes this identity to
the existing nondegenerate real four-dimensional frames. Reusing its native
incidence theorem gives

\[
(L_1+L_2)^2\ne0
\quad\Longleftrightarrow\quad
\operatorname{Disjoint}(\operatorname{span} L_1,\operatorname{span} L_2).
\]

Here `Disjoint` is disjointness of the two vector submodules, so their
intersection is the zero subspace. This equivalence uses that `2 ≠ 0` over
the reals. It does not assign a spacetime metric, a physical mass, or a screw
pitch to an exterior blade.

## 3. Compression brackets and projector curvature

For an arbitrary associative ring, let `p * p = p`, and write

\[
G(p;x,y)=px(1-p)yp,\qquad F(p;a,b)=p(ab-ba)p.
\]

The new declarations in `OperatorAlgebra/PeirceCompressionCurvature.lean`
reuse `OperatorDefectCompletion.compressed_commutator_defect` to establish

\[
[pxp,pyp]=p[x,y]p-G(p;x,y)+G(p;y,x).
\]

The existing `commutator_tangent` theorem supplies the tangent directions
`[x,p]` and `[y,p]`. Their ordered Gram tensor has the opposite sign:

\[
G(p;[x,p],[y,p])=-G(p;x,y).
\]

Consequently,

\[
[pxp,pyp]=p[x,y]p+F(p;[x,p],[y,p]).
\]

For commuting `x` and `y`, the first term vanishes. The resulting curvature
coefficient is already the one acting on the native Peirce submodule in
`PeirceProjectedConnection.projectedConnection_curvature`. The change does not
introduce another connection structure. It also records that if `x` commutes
with `p`, this inner-tangent curvature vanishes against every `y`.

## 4. Corrections and remaining interpretations

The supplied prose combines several mathematical carriers. The implementation
retains the distinctions needed for valid implications:

| Proposed interpretation | Exact status in this change |
| --- | --- |
| Every Klein point is a physical massless ray | Exterior decomposability and spacetime metric nullity remain separate. |
| Nonzero exterior square generates Dirac mass | The exterior incidence identity and the Dirac dispersion identity use different carriers; no map identifies their invariants. |
| Energy sign, chirality, and horizon support are the same projection | The energy idempotents are constructed from `H/E`; no such identification is assumed. |
| Compression necessarily creates nonzero curvature | The exact defect formula is provided, including an explicit vanishing condition. |
| Noncommuting velocity components force a helix | No trajectory, initial state, or expectation-value dynamics is constructed. |
| A momentum variable is central and satisfies nontrivial canonical commutation relations with position in the same algebra | Scalar momentum is restricted to the finite momentum fiber. A position representation requires a different carrier and a compatibility construction. |
| The massless limit produces a spacetime horizon | Only the longitudinal residual's zero-mass identity is supplied. |

Two signs in the source text require correction for the convention `[a,b]=ab-ba`:

- For commuting `x,y`, the first cross-corner term in `[pxp,pyp]` is negative,
  as proved above.
- If `beta` anticommutes with `Gamma5` and the kinetic term commutes with
  `Gamma5`, then `[H,Gamma5] = 2mc² beta Gamma5 = -2mc² Gamma5 beta`.
  This chirality identity is a correction to the prose, not an additional
  theorem introduced by this change.

Differentiating a momentum-dependent spectral projector, identifying its
curvature with a physical Berry connection, proving a gap-stability theorem,
or constructing Fock, modular, or horizon data remains separate work.

## 5. Focused validation surface

The declaration-level probe owner is
`InfoGeometry.Physics.DiracProjectionGeometryAudit`. It imports the three
branches and requests `#print axioms` for every new theorem-bearing declaration.
The `InfoGeometry` library already includes all submodules; no Lake or dependency
pin change is needed.

From a checkout with the pinned toolchain on `PATH`, run the maintained wrapper:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Physics.DiracProjectionGeometryAudit
```

The repository's staged and pre-push gates remain required. Source review,
placeholder scanning, successful compilation, and axiom acceptance are distinct
checks. Neither the existence of this probe owner nor the source-level reviews
establishes successful execution of those checks.

Source basis: repository revision `c143c264bc18bbf41d692be4e270b5b7f7405702`;
supplied note SHA-256
`0ca57bf40fa8288ba8f3e4c7c5b0b9fb2673f63d7ba4c00ca7473ef908ad6306`.
