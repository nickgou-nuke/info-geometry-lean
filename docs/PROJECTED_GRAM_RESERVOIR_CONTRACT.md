# Quaternion probes and an explicit GENERIC reservoir: theorem contract

## Source and scope

This supplement follows `NATIVE_PROSE_CONTRACT.md`. The new source is the
user-supplied `Pasted text (2)(20261117-130355).txt`, SHA256
`e86035703fb4a51469223dc1b5b5b2ff94b9a82a51d1feaf6d32c68cbdb5ad85`.
The attachment itself is not committed. Its claims are evidence to examine,
not instructions to assume a theorem or weaken an acceptance gate.

The two new owners have separate native contracts:

1. `Algebra.ZornQuaternionAssociatorGram` constructs the actual projection of
   both probe slots onto the ordinary quaternion subalgebra, and identifies
   the exact kernel of the resulting full bilinear Gram form.
2. `Thermo.GenericReservoirLift` constructs covector-to-vector operators on
   `V × ℝ` from supplied base operators, then derives the extended energy and
   entropy laws of the existing pointwise `GenericMetriplecticFlow.System`.

The full ambient-probe Gram owner remains separate. Its scalar kernel is
consistent with a quaternion kernel for the newly projected probe family.
Neither construction changes the nonassociative multiplication or supplies an
associativity instance for the full Zorn algebra.

Repository discovery starts from `08c34e03f610b452e03422037949196dc7d92d6d`.
The new Gram imports the repaired ambient owner in PR #384. The reservoir
imports existing baseline owners. Toolchain and dependency pins are unchanged.

## Existing owners and observed upstream overlap

| Source | Reused construction or observed scope | Remaining distinction |
| --- | --- | --- |
| `Algebra.ZornVectorMatrix` | Full real eight-dimensional alternative algebra with the actual dot/cross product | The full algebra remains nonassociative. |
| `Algebra.ZornPinorReconstruction` | Linear, injective, multiplication-preserving `quaternionEmbedding` | Associativity within its image does not imply vanishing against arbitrary ambient probes. |
| `Algebra.ZornCARAdjoint` | Strictly positive coordinate pairing `coefficientPairing` | This auxiliary pairing is distinct from the indefinite multiplicative split norm. |
| `Canonical.CattoGurseySplitBasis` | Actual eight-element signed basis `(E22,E11,V_i,-U_i)` | Its projected elements have factors `1/2`; they are not unit-normalized quaternion probes. |
| `Algebra.ZornAssociatorGram` | Full 64-pair ambient Gram, native associator adapters, and exact scalar-kernel target | Restricting both probe arguments creates a different form. |
| `Thermo.GenericMetriplecticFlow` | Native covectors, full operators, `System`, flow, energy conservation, and entropy nonnegativity | A `System` is pointwise algebra; it does not construct a manifold Poisson bracket or trajectory. |
| `Thermo.BilinearMetriplecticReduction` | Congruence through an actual inverse duality for a nondegenerate bilinear form | Its inverse cannot be applied directly to a degenerate associator Gram. |
| [PR #385](https://github.com/nickgou-nuke/info-geometry-lean/pull/385), observed head `ebfd3b1faff4fa2bda62c4ab0b44d51154abdf73` | Real Dirac-current constructions and an energy-orthogonal projection of the state/force with supplied associator probes | It does not supply the quaternion projection of both probe slots or this added entropy-coordinate lift. Its repaired native check was pending when inspected. |
| [PR #386](https://github.com/nickgou-nuke/info-geometry-lean/pull/386), observed head `1838b7dfc27cac18937136f6e4c168a8dc314e29` | Exact intake for the separate attachment SHA256 `bf9f75a5f439dfc01b3b39510e58facd4f3ea22ae7462e63f63f6046849e181c`; native metric compatibility, oblique counterexample, and phase-space consumer | No duplicate owner is introduced here. Its repaired native check was pending when inspected. |

The overlap search covered related owner definitions, their hypotheses,
imports and consumers, actual product/duality operations, and current upstream
PR sources. It is a bounded source search, not a complete live graph certificate.

## Quaternion-projected Gram

Write the existing vector Zorn carrier as `X = (a,v,w,b)`. The new linear maps
extract the two quaternion components

\[
q_0=\left(\frac{a+b}{2},\frac{w-v}{2}\right),\qquad
q_1=\left(\frac{a-b}{2},\frac{v+w}{2}\right).
\]

With the actual embedding and `ell = diagonal 1 (-1)`, the owner proves

\[
X=\operatorname{emb}(q_0)+\operatorname{emb}(q_1)\ell.
\]

The projector is the native composition
`quaternionEmbedding.comp quaternionPart`. Its actual coordinates are

\[
P_HX=\left(\frac{a+b}{2},\frac{v-w}{2},
                 \frac{w-v}{2},\frac{a+b}{2}\right).
\]

It is idempotent, fixes exactly `quaternionEmbedding.range`, and its residual
is orthogonal to that image for `coefficientPairing`. These facts are derived
from the coordinates; they are not supplied as projection hypotheses.

For the existing signed basis `e_i`, the form is the complete ordered sum

\[
G_H(X,Y)=\sum_{i,j\in I_8}
B_+([X,P_He_i,P_He_j],[Y,P_He_i,P_He_j]).
\]

Every state remains in the full ambient algebra. Only the two probe slots are
projected. Both diagonal basis elements give `emb(1)/2`; each color pair gives
two copies of `emb(i)/2`, `emb(j)/2`, or `emb(k)/2`. All 64 terms and all these
factors are retained. The attachment's suggestion that some projected basis
elements equal `i` and `j` literally is corrected by the explicit factors.

The converse kernel proof uses the native ordered product identity

\[
(\operatorname{emb}(q)\ell)\operatorname{emb}(p)
 =\operatorname{emb}(q\overline p)\ell,
\]

and therefore

\[
[\operatorname{emb}(q)\ell,\operatorname{emb}(i),\operatorname{emb}(j)]
 =2\operatorname{emb}(qk)\ell.
\]

The factor `k` acts on the right. Reversing the probe order or changing the
pair-product convention would change the calculation. Strict positivity of
`B_+` makes each vanishing Gram summand a vanishing associator. The nonzero
scaled `i,j` probe detects every transverse quaternion coordinate, using
Mathlib's actual quaternion multiplication and absence of zero divisors.

| Declaration | Exact contract |
| --- | --- |
| `quaternionProjector_idempotent`, `quaternionProjector_eq_self_iff`, `quaternionProjector_orthogonal` | A constructed coefficient-orthogonal projection with exactly the ordinary quaternion image as its fixed set |
| `quaternion_decomposition`, `quaternion_mul_ell_mul_quaternion` | The actual `H + H ell` decomposition and ordered product adapter |
| `associator_quaternion_mul_ell_i_j`, `associator_quaternion_i_j_zero_iff` | The ordered defect and its exact detection of membership in the quaternion image |
| `quaternionProbe_singlets`, `quaternionProbe_colors` | Explicit normalization of the actual projected signed basis |
| `quaternionAssociatorGram_symm`, `quaternionAssociatorGram_nonneg` | Symmetry and positive semidefiniteness of the constructed native bilinear form |
| `quaternionAssociatorGram_zero_iff_mem_range`, `quaternionAssociatorGram_left_kernel_iff_mem_range` | Both the quadratic zero set and the bilinear left kernel equal `quaternionEmbedding.range` |
| `quaternionAssociatorGram_embedding_zero`, `quaternionAssociatorGram_ell_pos` | Embedded quaternion states have zero value; the explicit complementary state `ell` has positive value |

The ambient form still has the scalar-line kernel. The projected form has the
quaternion-image kernel. A rank or finite-dimension conclusion requires its
own theorem and is not substituted for the exact set equalities proved here.

## Explicit reservoir lift

Let `V` be a real module, `h : Covector V`, `T > 0`, and
`L D : Covector V →ₗ[ℝ] V`. The base hypotheses are exactly

\[
\alpha(L\beta)=-\beta(L\alpha),\qquad
\alpha(D\beta)=\beta(D\alpha),\qquad
0\leq\alpha(D\alpha).
\]

No base injectivity, inverse symplectic form, finite-dimensionality, or
strictly positive mobility is required for the main constructor. Construct

\[
i(v)=(v,0),\quad A_h(v)=(v,-T^{-1}h(v)),\quad
d\widetilde H(v,s)=h(v)+Ts,\quad dS(v,s)=s,
\]
\[
\widetilde L=iLi^*,\qquad \widetilde M=T^{-1}A_hDA_h^*.
\]

The dual maps are actual pullbacks of linear covectors. Direct evaluation gives
`i.dualMap dS = 0` and `A_h.dualMap dH = 0`; hence both extended Casimir laws
are derived. The same congruence derives symmetry and nonnegativity of
`liftedDissipative`. Every original operator entry is retained.

The resulting existing `System.flow` has components

\[
\left(Lh-T^{-2}Dh,\;T^{-3}h(Dh)\right).
\]

The mechanical energy rate is `-T⁻² * h(Dh)`. The entropy-coordinate rate
multiplied by `T` cancels it. Total energy conservation and nonnegative entropy
evaluation are the existing `System` consequences, now applied to this
constructed system rather than to assumed extended operators.

| Declaration | Exact contract |
| --- | --- |
| `entropyCovector_ne_zero`, `energyCovector_ne_zero` | The added entropy covector is nonzero; the extended energy covector is nonzero when `T ≠ 0` |
| `energyTangentLift_dual_energy` | Direct computation of the energy-annihilating pullback for `T ≠ 0` |
| `liftedReversible_skew`, `liftedReversible_entropy` | Skewness inherited from `L` and the constructed entropy Casimir |
| `liftedDissipative_pairing`, `liftedDissipative_symmetric`, `liftedDissipative_nonneg` | Arbitrary-covector congruence formula, symmetry, and positive semidefiniteness |
| `liftedDissipative_energy`, `liftedDissipative_apply` | Derived energy degeneracy and both output blocks |
| `liftedDissipative_eq_zero_iff` | `M̃ α = 0 ↔ D (A_h.dualMap α) = 0`, requiring only `T ≠ 0` |
| `system`, `system_flow`, `system_entropy_rate`, `system_mechanical_energy_rate` | Construction of all five existing GENERIC algebra laws and exact flow/rate formulas |
| `system_flow_zero_of_energy_zero` | At `h = 0`, the full flow vanishes, even though the operator need not vanish |
| `liftedDissipative_reducedSharp` | Existing nondegenerate bilinear reductions lift by composition of their actual image map with `A_h` |

The construction contains inverses of `T`; it avoids division by `h` or its
norm. A nonzero entropy covector does not imply strictly positive production.
The dissipative kernel is the pullback of `ker D`, and need not be the energy
line. Calling `L ⊕ 0` corank one additionally requires suitable nondegeneracy
of the base operator and a finite-dimensional rank statement.

### The Gram-to-mobility boundary

A bilinear Gram form has covariant type `V →ₗ[ℝ] Covector V`. The reservoir
expects a mobility with the opposite type `Covector V →ₗ[ℝ] V`. An explicit
duality or Riesz construction is required to connect them. The new compatibility
theorem reuses `reducedSharp` only with its stated nondegenerate bilinear-form
hypothesis. Neither degenerate associator Gram is inverted. These owners do
not yet claim a fully instantiated Zorn reservoir evolution.

## Other corrections retained from the intake

The scalar-stress and exact halo results remain in PR #382. A new cored
rational profile is a prescribed alternative, separate from the paper's
equation (8). The following observations are mathematical source review,
not additional native declarations in these two owners:

- Only the gradient dyad has rank one. With `lambda = 1` and `v=(1,0,0,0)`,
  the full canonical stress is `I₄/2`.
- `q=u²` gives `3 * meanSpatialStress = energyDensity`; `q=3u²` gives zero
  mean spatial stress for nonzero coupling. Neither equality supplies isotropy
  or vanishing energy flux, so neither alone identifies a radiation or dust fluid.
- Noncollinear covectors do not always give noncommuting stress matrices.
  For `v=(1,1,1,1)` and `w=(1,-1,-1,-1)` at unit coupling, direct multiplication
  gives `T(v)T(w)=T(w)T(v)=I₄`. The existing existential noncommuting witness
  does not assert this false universal claim.
- The residual `-3H lambda Gamma` is nonzero only under nonvanishing hypotheses.
  The effective-pressure formula divides by `3H` and requires `H ≠ 0`.
- A mass asymptotic alone cannot be differentiated to obtain a density limit.
  For example, `M(r)=r³+r⁴ sin(1/r)` is asymptotic to `r³`, but its derived
  density contains the nonconvergent term `-cos(1/r)/(4π)` near zero.
- Anticommutation is a relation between the actual metric operators, not a
  consequence of positivity alone. The second attachment's correction is
  already developed in PR #386, including its explicit positive oblique example.
- Singular spinors remain included in the current/Fierz discussion. The
  observed PR #385 current construction does not by itself supply PDE,
  moving-observer flux, Cauchy-surface conservation, or a QFT local energy theorem.

The finite narrative graph gives an order for proposed dependencies. Its
height increases along edges, but some stated covers skip a height, so that
height is not a graded-poset rank. A designated terminal element does not
establish necessity, uniqueness, or physical consistency of a synthesis.

There are two independent constructive dependency chains. The Zorn product
and embedding give the actual projector and probe factors, then the Gram
form and its quaternion kernel. Separately, the base covectors and operators
give the inclusion, energy-tangent lift and pullbacks, then the extended
`System` laws and flow. Connecting a Gram to a mobility, realizing a Hamiltonian
differential and Poisson bracket, solving an ODE, or proving a Landauer
statement are separate constructions.

## Verification boundary

Independent source review checked the full projected Gram and reservoir
owners against the actual repository product, pairing, embedding, and pinned
Mathlib APIs. It found two recursive-extensionality proof risks; the isolated
candidates were repaired using explicit `LinearMap.ext`. No theorem statement,
operator order, or hypothesis was weakened.

Strict placeholder audits found no hard findings. Their two soft findings
concern the ambient basis-cardinality `decide` proof and the reservoir's
explicit section hypotheses. The semantic-vacuity error gate passed, with
one advisory on the direct coordinate formula `energyTangentLift_apply`.
These are source checks, not compiler warning or kernel results.

Native compilation and the complete declaration axiom audit remain required.
The focused workflow selects the ambient Gram, projected Gram, and reservoir
owners; their actual closure has 23 repository modules and 28 direct native
import roots. The workflow compiles that closure and requires
zero warnings in every selected owner. The maintained checker, foundational
axiom whitelist, exact dependency pins, and shared build lock are unchanged.
Static/source review and queued execution are not native acceptance. The
whole-root Lake integration gate remains a separate obligation.
