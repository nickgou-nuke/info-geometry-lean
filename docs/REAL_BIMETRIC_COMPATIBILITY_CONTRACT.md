# Real bimetric compatibility: theorem contract

## Problem and provenance

The intake infers anticommutation of a complex endomorphism and a para
involution from a common symplectic form and positivity of the compatible
metric. Positivity excludes commutation, but it does not establish
anticommutation. The missing condition is preservation of the compatible
metric by the para involution. The intake also identifies an ordered product
as the comparison of two metrics before establishing the relation needed to
exchange the order of its factors.

Source: `Pasted text(20261117-095630).txt`, 33,409 bytes, SHA256
`bf9f75a5f439dfc01b3b39510e58facd4f3ea22ae7462e63f63f6046849e181c`.
The input's narrative, psychological descriptions, and claims of a unique
physical synthesis are preserved in the intake record but are not mathematical
premises. This implementation starts from upstream `main`
`08c34e03f610b452e03422037949196dc7d92d6d`; it has no dependency on the unmerged
PR #374 or PR #383 owners.

This is a contract for three Lean source owners. Their current verification
status is recorded separately in [the review record](REAL_BIMETRIC_COMPATIBILITY_REVIEW.md)
and the PR checks. A source statement or a mathematical review is not a native
compilation receipt.

## Carrier, operations, and signs

The general carrier is a real vector space `E`, with native
`LinearMap.BilinForm ℝ E` and `Module.End ℝ E`. Multiplication of endomorphisms
is composition, so `(I * K) x = I (K x)`. For a bilinear form `ω`, use its
existing native contractions:

\[
G(x,y)=\omega(x,Iy),\qquad H(x,y)=\omega(Kx,y).
\]

These are `ω.compRight I` and `ω.compLeft K`. No custom form, abstract inverse
metric, or record of desired conclusions is introduced.

The geometric hypotheses, when needed, are

\[
I^2=-1,\quad K^2=1,\quad
\omega(Ix,Iy)=\omega(x,y),\quad
\omega(Kx,Ky)=-\omega(x,y).
\]

Alternation and nondegeneracy are explicit premises for the symmetry and
nondegeneracy results. Pinned Mathlib's `Nondegenerate` is two-sided. The
central compatibility equivalence needs only separation in the second slot.
Strict positivity is an additional premise wherever it is used.

## General owner

Owner: `lean/InfoGeometry/Geometry/SymplecticMetricCompatibility.lean`.

| Declaration | Exact implication and hypotheses |
|---|---|
| `complex_skew` | `I² = -1` and preservation of `ω` imply `ω(Ix,y) = -ω(x,Iy)` |
| `involution_skew` | `K² = 1` and reversal of `ω` imply `ω(Kx,y) = -ω(x,Ky)` |
| `compRight_isSymm`, `compLeft_isSymm` | The preceding compatibility and alternation make the actual contractions symmetric |
| `compRight_nondegenerate`, `compLeft_nondegenerate` | Nondegeneracy and the respective square law make each contraction nondegenerate; no finite dimension is needed |
| `isometry_iff_anticommute` | Right separation, `K² = 1`, and reversal of `ω` give `G(Kx,Ky) = G(x,y)` for all vectors iff `I*K = -(K*I)`; no positivity, alternation, or complex square law is needed |
| `metric_intertwiner` | The complex square/preservation laws and `K² = 1` give `H.compLeft (-(K*I)) = G`, without anticommutation |
| `metric_intertwiner_unique` | With nondegenerate `ω`, any endomorphism `T` satisfies `H.compLeft T = G` iff `T = -(K*I)` |
| `mul_sq_eq_one_iff_anticommute` | Under the opposite square laws, `(I*K)*(I*K) = 1` iff `I*K = -(K*I)` |
| `not_commute_of_positive` | Strict positivity of `G`, an anti-symplectic involution `K`, and a nontrivial carrier exclude `I*K = K*I` |
| `compLeft_ne_of_opposite_squares` | A nondegenerate common form cannot have equal left contractions by maps with opposite square laws on a nontrivial real carrier |

The fixed-form uniqueness argument reuses Mathlib's
`LinearMap.BilinForm.compLeft_injective`. It does not reconstruct
`g⁻¹ω`; existence of such an inverse in infinite dimension would need more
than weak nondegeneracy. The nontriviality assumptions prevent a false
contradiction on the zero vector space.

## Full finite counterexample

Owner: `lean/InfoGeometry/Geometry/ObliqueSymplecticInvolution.lean`.
Reuse `Canonical.ParaHyperkahlerPresymplecticBridge` and its actual real
two-dimensional matrix frame. The new family is

\[
\Omega=\begin{pmatrix}0&1\\-1&0\end{pmatrix},\qquad
I=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\qquad
K_a=\begin{pmatrix}1&a\\0&-1\end{pmatrix}.
\]

The existing frame's `I_mat` has the opposite sign from this positive
right-slot convention. The source uses `-I_mat` and builds
`K_a = K_mat + (a/2) • (J_mat + I_mat)`. `Matrix.toBilin'` and `Matrix.toLin'`
provide the actual bilinear form and endomorphisms, retaining the full matrix
products and vector carrier.

For every real `a`, the native statements include:

\[
I^2=-1,\quad K_a^2=1,\quad K_a\ne\pm1,\quad
I^T\Omega I=\Omega,\quad K_a^T\Omega K_a=-\Omega,
\]

\[
G(x,y)=x_0y_0+x_1y_1,\qquad
IK_a+K_aI=a\,1.
\]

The actual native eigenspaces are

\[
L_+=\mathbb R(1,0),\qquad L_-=\mathbb R(-a/2,1).
\]

Each has `Module.finrank` one and is isotropic for `ω`; their displayed
generators have symplectic pairing one. Thus the counterexample retains the
source's equal-rank para-complex requirement. The operators never commute,
and anticommutation and preservation of `G` each hold exactly at `a = 0`.

At `a = 1`, the source collects all hypotheses and both failed operator
relations in `positive_compatible_counterexample`. An explicit vector pair
also witnesses failure of the proposed `IK` metric comparison:

\[
H((IK_1)e_0,e_1)=1\ne0=G(e_0,e_1).
\]

This is a two-dimensional counterexample to an overstrong implication. It is
not presented as a neutral hypersymplectic four-dimensional model.

## Existing phase-space consumer

Owner: `lean/InfoGeometry/Clifford/PhaseSpaceSymplecticMetricCompatibility.lean`.
The carrier remains the existing `PhaseSpaceCarrier E = E × Module.Dual ℝ E`.
`MetricDatum E` is the existing symmetric duality equivalence `gFlat`. It does
not assume positivity and does not assert that every algebraic vector space
admits such an equivalence.

Let `K = neutralParaInvolution`, `I = -phase G`, and
`S = (ofMetric G).polarization`. The new readbacks are

\[
\omega(KX,Y)=\mathrm{canonicalNeutralBilin}(X,Y),\qquad
\omega(X,IY)=\mathrm{generalizedMetricForm}(X,Y),
\]

\[
IK=S,\qquad KI=-S.
\]

The source establishes preservation/reversal of the same `neutralOmega`,
applies the general anticommutation criterion to the existing generalized
metric, and identifies `S` as its unique comparison with the neutral metric.
The two uses of imported `neutralOmega_nondegenerate` retain
`Module.Projective ℝ E` explicitly. Positivity is reused through the existing
`ParaKahlerGeneralizedMetric.generalizedMetricForm_pos`, under its actual
positive base-metric premise. No new carrier, operator, metric, or positivity
axiom is added by this consumer.

## Established dependency order

The square laws yield invertibility and the relevant skew identities.
Alternation then yields symmetry of the contractions, while nondegeneracy
passes through their invertible factors. Reversal by `K` and right separation
yield the exact isometry/anticommutation equivalence. Complex skewness and
`K² = 1` yield the ordered comparison `-KI`; nondegeneracy gives uniqueness.
Positivity and nontriviality separately exclude commutation.

The explicit matrix family supplies a counterexample independently of the
general theorem. The phase-space consumer uses the general theorem and the
existing owners' actual maps. These are dependency edges between stated
maps and implications, not a causality claim about the source's narrative.

## Existing results and explicit boundaries

The bounded owner survey inspected 47 relevant owner/consumer files and their
imports. Native `compLeft_injective` supplies fixed-form uniqueness. Existing
`ParaKahlerLagrangianDimension` and `ParaKahlerSymplecticLagrangian` own generic
para eigenspace dimension/isotropy results. `FlatSplitQuaternionGeometry`,
`FlatSplitQuaternionPotential`, and `FlatSplitQuaternionFamily` already supply
the genuine single-neutral-metric model, its finite products, and actual
exterior-derivative readbacks. `Cl11Matrix.cl11EquivMat` owns the native
Clifford/matrix equivalence. These constructions are not reimplemented here.

The following source claims are corrected or excluded:

- A general factor-of-four/signature theorem is outside this change. Its
  proposed proof incorrectly treats `I` as an endomorphism of a single
  `K`-eigenspace, although anticommutation exchanges the eigenspaces. The
  repaired argument needs a nondegenerate alternating form restricted to one
  leaf and a parity proof for that restricted form.
- Nonzero third derivatives do not imply curvature or distinct Levi-Civita
  connections. A source-audit countermodel on `x > 0` takes `Ψ = x²y`,
  `ω = 2x dx∧dy`, `H = 4x dx dy`, and `G = 4x² dx² + dy²`.
  In `u = x², v = y`, both metrics are constant and share the same flat
  connection, despite `Ψ_xxy = 2`. This differential countermodel is recorded
  as mathematical audit evidence; it is not formalized by these algebraic
  owners.
- The Hessian cubic measures nonmetricity or connection difference, not
  torsion. Strict convexity alone does not guarantee an invertible Hessian.
- Fisher/BKM identifications require an actual statistical or quantum model.
  A symplectic form and a positive metric alone do not supply full
  metriplectic Casimir degeneracies, trajectories, or a dissipative flow.
- Nonassociative multiplication can make `L_a L_b - L_(ab)` nonzero. Each
  `L_a` remains a linear endomorphism, and endomorphism composition remains
  associative. No exchange of these two products is licensed here.
- A chosen top vertex in a finite poset establishes no uniqueness or
  necessity of a geometric or physical synthesis.

Primary context: H. Sakamoto, [A Born structure on the tangent bundle of a
Hessian manifold](https://link.springer.com/article/10.1007/s41884-026-00215-5),
especially §§2.2–2.5 and Lemma 2.18. Its hypotheses separately state the
para-hypercomplex and metric compatibilities. It supplies context for the
audit, not authority for Lean elaboration or a manifold-level claim in this PR.
