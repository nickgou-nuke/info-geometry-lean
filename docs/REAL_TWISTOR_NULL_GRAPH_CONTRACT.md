# Real phase-compatible null incidence graphs

## Source and intent

Source: R. Penrose and M. A. H. MacCallum, *Twistor Theory: An Approach to the
Quantisation of Fields and Space-Time*, Physics Reports 6(4), pp. 241–316,
DOI `10.1016/0370-1573(73)90008-2`. Relevant passages: the twistor pairing
in equation (1.37), the passive translation in (2.1), and the incidence and
null-plane discussion surrounding (2.11)–(2.12), printed pp. 255–260.

The supplied scan has SHA-256
`ab722666c30b5946d0a4d56c7bfe8889c9ea3590d791aca826647b298bf2fc79`.
The original attachment is retained by the user; this change does not vendor
the paper. Source equations were checked visually as well as by text extraction.

Repository baseline: `586c14bc9fb94eb09b56f7dc850d9d5297269f91`.
Lean: `leanprover/lean4:v4.34.1`.
Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

The task is to connect the existing real graph-incidence API to the existing
neutral metric and an internal real phase operator. This is an algebraic
graph-chart result, with exact converse and uniqueness statements.

## Existing source owners and bounded search

The canonical `lean/` tree and parallel `src/` tree were searched for incidence,
reconstruction, graph intersections, isotropy, Witt/neutral forms, skew
operators, and phase commutation; the relevant imports and consumers were
inspected. Documentation and filenames served only as navigation.

| Owner | Reused or adjacent content |
|---|---|
| `Twistor/RealTwistorIncidence.lean` | `incidenceMap`, `incidenceSpace`, `mem_incidenceSpace`, `incidenceSpace_injective`, `translation`, `shared_nonzero_twistor_iff` |
| `Krein/Metric.lean` | `hessian_indefinite_formCoord`, the actual off-diagonal form on `E × E`, and its established rotation to the diagonal doubled form |
| `Twistor/RealTwistorSoldering.lean` | Existing split-signature `(2,2)` soldering and null-intersection theorem; not re-proved or relabeled Lorentzian |
| `Twistor/RealMultiTwistorReconstruction.lean` | Reconstruction from a spinor basis |
| `Twistor/PerjesConventions.lean` | Existing complex two-spinor incidence isotropy |
| `Twistor/TwoTwistorIncidenceIsotropy.lean` | Existing finite complex invertible-frame converse |
| `Twistor/PenroseRealDoubledPeirceSoldering.lean` | Existing carrier equivalences, explicitly without quadratic-form transport |
| `Quantum/RealKCategory.lean` | Real modules with internal square-minus-one phase and their categorical equivalence with complex modules |
| `Geometry/IndividuatedUHP.lean` | A phase/self-adjoint/skew composition theorem for a more specialized continuous doubled carrier |

The missing implication identified in this inspected surface is a general real
classification of phase-invariant, totally isotropic native incidence graphs.
This is not an assertion that all twistor geometry was previously absent.

## Exact mathematical contract

Let `E` be a real inner-product space. No completeness or finite-dimensional
assumption is required. The carrier is the existing `E × E`; operators are
native `Module.End ℝ E`, with composition as multiplication.

The existing graph and pairing are

\[
L_A=\{(Au,u):u\in E\},\qquad
g((\omega,\pi),(\xi,\eta))=
\langle\omega,\eta\rangle+\langle\xi,\pi\rangle.
\]

The principal result assumes exactly

\[
J^2=-1,\qquad
\langle Ju,v\rangle=-\langle u,Jv\rangle.
\]

It proves

\[
\begin{aligned}
&g|_{L_A\times L_A}=0\quad\text{and}\quad
(J\oplus J)L_A\subseteq L_A\\
&\quad\Longleftrightarrow\quad
\exists!X:\ X\text{ is inner-product symmetric},\quad JX=XJ,
\quad A=JX.
\end{aligned}
\]

The reconstruction is the explicit operator `-(J * A)`, not a structure field
or an assumed reconstruction witness. Symmetry is native `LinearMap.IsSymmetric`;
for an arbitrary noncomplete space it is not presented as existence of an
analytic adjoint. Commutation of two different spacetime operators is never
assumed.

Supporting results establish total isotropy iff skewness, graph phase invariance
iff commutation, the exact translation pairing defect, preservation of the
neutral form iff the translation operator is skew, self-orthogonality and
maximal total isotropy of skew graphs, and cancellation of the phase in the
existing common-vector/kernel criterion.

For a native submodule `L`, the extended theorem assumes that
`(LinearMap.snd ℝ E E).comp L.subtype` is bijective. The graph owner constructs
its native inverse with `LinearEquiv.ofBijective`, obtains the unique graph
operator, and transfers the classification to `L`. This chart inverse is
generally noncomputable; it uses Mathlib's classical inverse construction.
The explicit `-(J * A)` reconstruction for a given graph operator is separate
from this inverse-projection construction. Injectivity alone is not substituted
for bijectivity in infinite dimension.

The examples use the existing `clockAxis` on `DoubledSpace ℝ`. They prove its
square-minus-one and skew laws, exhibit a nonzero vector in its null graph,
and prove that the identity graph has a vector of neutral square two. The
operator `-clockAxis` commutes with the clock but fails symmetry, demonstrating
why the symmetry condition is necessary. This example has two real spinor
dimensions and makes no Lorentzian spacetime claim.

## Dependency order

1. Existing graph parametrization and neutral metric.
2. Isotropy/skewness and phase-invariance/commutation equivalences.
3. Explicit inverse phase rotation and its two inverse identities.
4. Unique symmetric reconstruction.
5. Existing graph intersection theorem, followed by injective phase cancellation.

Translation preservation uses the exact graph pairing defect. Maximality uses
the proved orthogonality criterion. These are proof dependencies, not analogies.

## Interpretation boundaries

The paper's Hermitian signature `(2,2)` realifies to signature `(4,4)` on eight
real dimensions. The current generic theorem does not itself construct the
four-dimensional Lorentzian soldering or identify that realification.

The graph is assumed to be in the affine chart. The arbitrary-subspace extension
includes the explicit transversality condition on the second projection.
The real projectivization already in the graph owner is not automatically the
paper's complex projective twistor space.

The existing plus-sign `translation` is an active shear; the paper's passive
origin change uses the inverse shear. Neither is called a boost. The
infinity twistor, conformal-group coverings, analytic Penrose transform,
scattering amplitudes, and quantum gravity are outside this change.

## Validation status

Implementation: `lean/InfoGeometry/Twistor/RealTwistorIsotropicGraph.lean`, the
two graph-chart lemmas in `RealTwistorIncidence.lean`, and
`RealTwistorIsotropicGraphExamples.lean`. The theorem module is imported by
the existing `RealConstructs.lean` umbrella.
Compilation, declaration axiom audit, independent semantic review, and independent
QA are separate gates. Results are recorded only after those commands run.
The root workspace and any focused verification package have different coverage;
success of the latter does not certify the whole repository.
