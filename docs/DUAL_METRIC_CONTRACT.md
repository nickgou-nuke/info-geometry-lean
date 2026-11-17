# Real symplectic compatibility and dual metric operators

## Input and mathematical status

This contract extracts the real operator and bilinear-form statements from
`Pasted text(20261117-124556).txt`, SHA256
`bf9f75a5f439dfc01b3b39510e58facd4f3ea22ae7462e63f63f6046849e181c`.
The implementation base is `08c34e03f610b452e03422037949196dc7d92d6d`.
The dependency pins remain Lean `4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

All new statements use real modules, real bilinear forms, real matrices, or the
existing full real split-octonion carrier. No external complex scalar model is
substituted for the operators. Native endomorphism and matrix multiplication
retain their noncommutative order. The split-octonion carrier retains its
nonassociative multiplication.

The files contain complete proposed Lean proofs. Their native acceptance status
is recorded separately in [DUAL_METRIC_VERIFICATION.md](DUAL_METRIC_VERIFICATION.md).
A source review or a published draft is not a kernel-verification certificate.

## Existing owners and the smallest missing implications

Paths in this table are relative to `lean/InfoGeometry` unless otherwise stated.
The search inspected definitions, assumptions, imports, and actual consumers in
these related owners; it is a bounded source audit, not a repository-wide absence
certificate.

| Existing owner | Actual construction and hypotheses | Reuse and remaining gap |
|---|---|---|
| Mathlib `LinearAlgebra/BilinearForm/Properties` | Native `BilinForm.compLeft`, `compRight`, two-sided `Nondegenerate`, and `compLeft_injective` | Reuse form-determined operator uniqueness; derive the incompatible-square obstruction and the precise complex/product compatibility implications. |
| Mathlib `LinearAlgebra/SesquilinearForm/Basic` | `IsSkewAdjoint` and `IsAdjointPair.mul`, which reverses the adjoint product order | Reuse this API for the shared-metric skew-adjoint product result. |
| `Clifford/NeutralPhaseSpaceCore` | `PhaseSpaceCarrier E = E × Module.Dual ℝ E`; evaluation-based neutral bilinear form, real grading `K`, and `neutralOmega` | Reuse the actual primal/dual carrier and form normalizations. Nondegeneracy is separately proved there with its projectivity hypothesis. |
| `Clifford/PhaseSpaceGeneralizedMetric` | `MetricDatum.gFlat : E ≃ₗ[ℝ] E*`, with symmetry; actual zero-B polarization and generalized bilinear metric | Invertibility and symmetry are inputs. Positivity is not a field of the datum. No new metric carrier is needed. |
| `Clifford/ParaKahlerGeneralizedMetric` | `phase = K*S`, square minus one, anticommutation, and generalized-metric positivity under explicit positive base duality | Its phase has the negative right-slot convention. The missing bridge is `I = -phase` and its exact contractions by the existing symplectic form. `Cl55ParaKahlerMetric` is an existing consumer. |
| `Geometry/ParaHessianMixedPotential` | Existing real doubled flat potential, its actual Fréchet derivatives, exchange/grading operators, and mixed metric/symplectic signs | Retain this analytic owner. It already supplies the flat potential; it does not supply a variable-curvature or general statistical-manifold theorem. Consumers include `ParaHessianMetriplecticCompatibility` and `Lie/SplitOctonionParaHessianBridge`. |
| `Krein/DoubledSpace` and `Canonical/RealMirrorComplexStructure` | Real doubled complex operator, product table, and a native real square-minus-one predicate; mirror anticommutation is an explicit hypothesis | These are existing real structures. They do not imply positivity or a statistical interpretation from square identities alone. |
| `Algebra/HypercomplexTriad` | Exact real 2-by-2 matrices `I`, `E`, `N` and their square identities | Reuse these matrices to construct `K_b = E + b*N`, which disproves automatic anticommutation. |
| `Canonical/ParaComplexNeutralForm` | Symmetric-form anti-compatibility and isotropic projector results | Its datum assumes a symmetric form and compatibility. It does not replace the alternating-form contraction equivalence proved here. |
| `Canonical/Sp4ParaHyperkahlerPresymplecticBridge` and `ParaHyperkahlerFisherClosureWave24` | Concrete real 4-dimensional operators and form readouts | These are examples with a left-slot convention, not a generic positive right-slot equivalence or a statistical-model theorem. |
| `Canonical/SplitOctonionRegularOperators` | Actual left/right regular linear maps, associator, and the exact criterion for regular composition to equal multiplication by a product | Reuse the full quaternion-pair carrier. An element-level anticommutation identity does not by itself prove operator anticommutation. |
| `Canonical/SplitOctonionRegularEllipticOperators` and `SplitOctonionRegularProjectors` | Actual elliptic and hyperbolic operators, separate normalized square laws, and complementary hyperbolic projectors | Derive their joint anticommutation, ordered-composite square, and projector exchanges. Existing consumers include `SplitOctonionDoubledLoxodromic`, `SplitOctonionBogoliubovGeneratorBridge`, and `SplitOctonionHyperbolicFunctionalCalculus`. |

## Native theorem contracts

### 1. General real bilinear forms

Owner: `InfoGeometry.Geometry.SymplecticComplexParaCompatibility`.

Let `V` be a real module and `I,K : Module.End ℝ V`. Multiplication means
endomorphism composition, so `(I*K) v = I (K v)`. Set

\[
g_I(u,v)=\omega(u,Iv),\qquad g_K(u,v)=\omega(Ku,v).
\]

The source derives the following implications with their actual hypotheses:

- On a nontrivial module, a nondegenerate bilinear form `g` cannot satisfy
  `g.compLeft I = g.compLeft K` together with `I*I = -1` and `K*K = 1`.
  Native injectivity first gives `I=K`; the square signs then contradict a
  nonzero real vector. Symmetry of `g` is unnecessary for this obstruction.
- Symplectic preservation by a square-minus-one `I` gives
  `omega (I u) v = -omega u (I v)`. Antisymplectic preservation by a
  square-one `K` gives the analogous identity for `K`.
- If `omega` is alternating, those identities make `g_I` and `g_K` symmetric.
  Nondegeneracy follows from nondegenerate `omega` and the corresponding square
  identity; it does not require positivity or finite dimension.
- With `I*K = -(K*I)`, the exact ordered bridge is

  \[
  g_K((IK)u,v)=g_I(u,v).
  \]

  Reversing the order gives `g_K((KI)u,v) = -g_I(u,v)`. This reversed-order
  identity already follows from the square identities and symplectic
  preservation by `I`; it does not need anticommutation.
- For nondegenerate `omega`, antisymplectic `K`, and `K*K=1`,

  \[
  g_I(Ku,Kv)=g_I(u,v)\ \text{for all }u,v
  \quad\Longleftrightarrow\quad IK=-KI.
  \]

  This equivalence does not require positivity, alternation, or `I*I=-1`.
  Strict positivity of `omega v (I v)` on nonzero vectors excludes *commuting*
  `I,K` on a nontrivial module; it does not prove anticommutation.
- For one bilinear form `g`, if `I` and `K` are native `g`-skew-adjoint and
  anticommute, their ordered product `I*K` is also `g`-skew-adjoint. If `g` is
  symmetric, `g.compLeft (I*K)` is alternating. These last two statements are
  algebraic and assert no manifold, signature, or dimension classification.

### 2. The existing cotangent metric, with a positive right-slot convention

Owner: `InfoGeometry.Clifford.PositivePhaseMetricBridge`.

A chosen `MetricDatum E` supplies a symmetric real duality equivalence
`gFlat : E ≃ₗ[ℝ] E*`. On the existing `E × E*`, use

\[
\begin{aligned}
K(x,p)&=(x,-p),\\
I(x,p)&=(-g^\sharp p,g^\flat x),\\
S(x,p)&=(g^\sharp p,g^\flat x).
\end{aligned}
\]

Here `I = -phase`, and `S` is the existing zero-B generalized-metric
polarization. The new owner proves `I^2=-1`, `IK=-KI`, and `IK=S`.
It proves preservation of the actual `neutralOmega` by `I`, and the native
bilinear-form equalities

\[
\begin{aligned}
\omega(X,Y)&=q(x)-p(y),\\
B(X,Y)&=p(y)+q(x)=\omega(KX,Y),\\
H_G(X,Y)&=g^\flat(x)(y)+p(g^\sharp q)=\omega(X,IY),\\
B((IK)X,Y)&=H_G(X,Y),\\
B((KI)X,Y)&=-H_G(X,Y).
\end{aligned}
\]

The two intertwining results consume the generic form theorems above.
The final positive diagonal result reuses the existing generalized-metric
positivity theorem under the explicit hypothesis
`forall x, x != 0 -> 0 < gFlat x x`.

In finite real coordinates this is the algebraic block pattern
`I = [[0,-g^-1],[g,0]]` and `H_G = diag(g,g^-1)`. Identifying a varying `g`
with a Hessian and constructing a Kähler manifold require separate differential
data. The new owner does not reconstruct the already existing flat potential
or assume a Fisher/BKM interpretation.

### 3. Concrete counterexample to automatic anticommutation

Owner: `InfoGeometry.Examples.PositiveCompatibleNonAnticommuting`.

Reuse the canonical real matrices and construct

\[
I=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\quad
K_b=E+bN=\begin{pmatrix}1&b\\0&-1\end{pmatrix},\quad
\omega(u,v)=u_0v_1-u_1v_0.
\]

The native bilinear form is `Matrix.toBilin' (-I)`. It is alternating and
nondegenerate. The source proves

\[
\omega(Iu,Iv)=\omega(u,v),\quad
\omega(u,Iv)=u\mathbin{\cdot}v,\quad
K_b^2=1,\quad
\omega(K_bu,K_bv)=-\omega(u,v).
\]

Strict positivity follows for nonzero `u` from the real dot product.
Nevertheless,

\[
IK_b+K_bI=b\,1.
\]

Thus `I` and `K_b` anticommute exactly when `b=0`. They never commute.
The actual eigenspace equations are also proved:

\[
K_bu=u\iff u_1=0,\qquad
K_bu=-u\iff u_0=-(b/2)u_1.
\]

For every nonzero `b`, this gives a positive-compatible counterexample with
two genuine distinct eigenlines. There is no dichotomy saying that two
square-sign operators must either commute or anticommute.

### 4. Actual split-octonion regular operators

Owner: `InfoGeometry.Canonical.SplitOctonionEllipticHyperbolicBridge`.

Use the existing eight-dimensional real quaternion-pair carrier, with
`I_g = leftRegular (I_gen g)` and `K_h = leftRegular (J_g h)`.
From `star g = -g`, the source derives both anticommutation orders by the
actual quaternion component multiplication. Neither normalization is needed
for that identity. With both quaternion norms equal to one, it reuses the
existing separate square laws to derive `(I_g o K_h)^2 = id`.

Both existing projectors are exchanged:

\[
I_gP_+=P_-I_g,\qquad I_gP_-=P_+I_g.
\]

The corresponding eigenvector implications are proved on the full carrier.
Composition remains different from multiplication by the raw product:

\[
I_g(K_hz)-L_{(g,0)(0,h)}z=-[(g,0),(0,h),z].
\]

With the repository's quaternion convention, the concrete witness is

\[
[i,\ell,j]=-2k\ell,\qquad
(L_i\circ L_\ell-L_{i\ell})(j)=+2k\ell.
\]

The final inequality of operators is obtained from the existing associator
criterion. No associative matrix algebra is substituted for split-octonion
multiplication, and no positive inner product is inferred from its split norm.

## Corrections and differential boundaries

The input's strongest synthesis claims require the following corrections.

1. **Positivity and anticommutation are separate properties.** The real matrix
   family above disproves the asserted necessity. Replacing a compatible `I`
   by `-I` retains its square and anticommutation while negating the right-slot
   metric, so anticommutation alone cannot choose its positive sign.
2. **A positive metric is positive on nonzero diagonal vectors.** The assertion
   `g_I(u,v)>0` for all pairs is false; arbitrary mixed values can have either
   sign or be zero.
3. **Anticommutation swaps the two `K` eigenspaces.** It does not make `I` a
   complex structure on the `+1` eigenspace. In the finite-dimensional
   shared-neutral-metric setting, a correct dimension argument uses the
   nondegenerate alternating pairing `g(Iu,v)` restricted to one null half.
   That half then has even dimension, giving total dimension a multiple of
   four. This dimension argument is explanatory here, not a new Lean theorem.
4. **Algebraic compatibility does not assert differential closedness.** A
   hypersymplectic manifold additionally has the appropriate compatible
   structures and closed two-forms. The generic shared-metric theorems here
   prove only the pointwise skew-adjoint and alternating identities.
5. **A nonzero third derivative is not a curvature certificate.** For a mixed
   potential, `Psi(x,y)=xy+x^3` has nonzero pure third derivative and the same
   constant mixed Hessian as `xy`. Even in the positive cotangent block
   construction, on `x>0` the potential `phi=x log x-x` gives `g=1/x` and
   nonzero `phi'''=-1/x^2`, whereas `dx^2/x+x dy^2` becomes
   `dr^2+r^2 dtheta^2` under `r=2 sqrt x`, `theta=y/2`: it is locally flat.
   These countercalculations are explanatory, not claimed as new native
   differential-geometry proofs.
6. **Distinct connections and torsion are different claims.** Levi-Civita
   connections are torsion-free. In a specified Hessian statistical structure,
   cubic tensors can express differences among an affine connection, its dual,
   and the Levi-Civita connection. The operator relations do not construct
   those connections or prove their flatness or curvature.
7. **Thermodynamic and metriplectic identifications need more data.** A
   statistical model, a normalizable measure, observables, energy, entropy,
   and an appropriate dissipative operator are not selected by `I,K,omega`.
   A positive full-rank metric does not itself give the energy kernel of a
   metriplectic bracket. The present PR supplies no partition-function,
   heat-dissipation, Landauer, or uniqueness theorem.
8. **A ranked diagram is not a proof of a mathematical equivalence.** The
   implementation records actual imported owners and theorem implications.
   It does not encode the supplied narrative labels as axioms or claim a
   classification from an imposed terminal node.

The separate operator branches satisfy split-Clifford generator relations where
proved. A new universal Clifford-algebra representation, faithfulness theorem,
manifold integrability theorem, or analytic completion is not claimed merely
from those relations.

## Primary mathematical references for the boundaries

- H. Shima, [Vanishing theorems for compact Hessian manifolds](https://www.numdam.org/articles/10.5802/aif.1065/),
  Annales de l'Institut Fourier 36(3), 1986. Its Hessian structure includes a
  flat affine connection and a metric locally given by its second derivative;
  this is additional geometric data.
- L. C. de Andrés et al., [Bianchi type A hyper-symplectic and hyper-Kähler
  metrics in 4D](https://arxiv.org/html/1102.1518v2), Introduction. It distinguishes
  the paraquaternionic endomorphism algebra, the compatible neutral metric,
  and closedness of the three forms. The new Lean files cover only the stated
  algebraic implications, not the paper's manifold construction.

The imported owner statements and the exact pinned Mathlib APIs, rather than
the terminology in either prose source, determine the scope of the formal code.
