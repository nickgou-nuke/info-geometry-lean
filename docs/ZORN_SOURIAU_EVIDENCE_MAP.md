# Zorn operators and Souriau geometry: evidence and scope

## Assessment

The useful core is a real operator representation of a nonassociative
composition algebra, together with an exact incidence test. It permits native
Zorn calculations to be transported into associative endomorphisms and real
eight-by-eight matrices. The representation retains multiplication defects;
it does not make the Zorn product associative.

The intake's claim that the full `Cl(4,3)` embeds in `M₈(ℝ)` is false. The
repository already contains the opposite theorem. The split norm, a Clifford
action, Peirce projectors, and equal representation dimensions also do not by
themselves establish the advertised physical or triality identifications.

The attached Souriau proposal supplies a separate algebraic action-groupoid
problem and a finite partition-function problem. Its negative-graph reduction
has a sign error. These chains are kept separate until an actual compatibility
map is constructed.

## Native owner map

The status below concerns the mathematical content of source declarations.
Fresh native validation for this change is recorded separately in
`verification/zorn-souriau`; historical owner source is not a current build
certificate.

| Content | Owner and precise declaration | Scope |
|---|---|---|
| Faithful linear regular embedding | `Lie/CanonicalZornRegularOperators.lean`: `leftRegularRepresentation_injective` | Linear injectivity from evaluation at `1`; no preservation of arbitrary products |
| Clifford action | `Lie/SplitOctonionCliffordAction.lean`: `splitOctonionLeftCliffordRepresentation` | An algebra homomorphism from the native universal Clifford algebra |
| Obstruction to full faithfulness | `Lie/SplitOctonionCliffordNoninjective.lean`: `leftClifford_finrank`, `canonicalZornEnd_finrank`, `splitOctonionLeftCliffordRepresentation_not_injective` | Dimensions `128` and `64`; the generator map may still be injective |
| Left inverse and unit criterion | PR #441's `Lie/CanonicalZornRegularNorm.lean`: `leftRegular_mul_conj`, `conj_mul_leftRegular`, `isUnit_leftRegular_iff` | Every canonical Zorn element; reused directly rather than redeclared |
| Right inverse contractions and invertibility | New `Lie/SplitOctonionRegularInvertibility.lean`: right contraction identities, explicit unit, `rightMultiplication_bijective_iff`, `rightMultiplication_isUnit_iff` | Every canonical Zorn element; right invertibility iff its native norm is nonzero |
| Circular four-vector phase | New `Lie/ZornChiralCircularFourVectorOperators.lean`: `phaseVector`, `phaseVector_det`, `phaseVector_diagonal_det` | Actual Ell-circular basis and both four-dimensional Witt inclusions |
| Matrix incidence | Same new owner: `phaseVector_leftMatrix_singular_iff`, `phaseVector_rightMatrix_singular_iff` | Zero determinant of the existing full real `8 × 8` matrices iff the mixed pairing vanishes |
| Basic pole projectors | `Lie/SplitOctonionEllCircularOperatorCoordinates.lean`: `leftCoordinateOperator_uPlus_apply`, `leftCoordinateOperator_uMinus_apply` | Projection onto the first/last four coordinates; four-dimensional ranges |
| Separate CAR vacuum | `Algebra/Zorn/RegularCARVacuumSeparation.lean`: `vacuumProjector_range`, `vacuumProjector_ne_pole_action` | One-dimensional vacuum range, distinguished from regular multiplication by a pole |
| Exterior/Fock comparison | `Clifford/ExteriorZornCARIntertwiner.lean`: `exteriorZornCARLinearEquiv` and its creation/contraction intertwiners | A linear equivalence with compatible operators; not an associative Zorn-algebra equivalence |
| Affine cocycle | `Algebraic/CartanSouriauAffineCocycle.lean`: `Datum`, `affineAction_mul`, `theta_inv` | Action and cocycle laws are inputs; inverse and affine laws are derived |
| Typed affine groupoid | New `Algebraic/CartanSouriauActionGroupoid.lean`: `affineMulAction`, `AffineActionGroupoid`, `affineActionGroupoid_nonempty_hom_iff` | Native mathlib `ActionCategory` and its `Groupoid` instance |
| Bilinear graph restriction | New `Algebraic/CotangentBilinearGraph.lean`: `cotangentForm_pullback_signedGraph` | Native real bilinear forms on `V × Module.Dual ℝ V` |
| Finite negative log-partition | New `Analytic/FiniteNegativeLogPartition.lean`: `negativeLogPartition_midpoint`, `negativeLogPartition_permute_sub` | Nonempty finite index type; midpoint concavity and an explicit scalar shift hypothesis |

The exact requested module title was not found in the bounded baseline source,
default-branch code, and related-PR search. PR #441 was published during this
work and supplies the overlapping generic left-action results and a Cartesian
Witt bridge. This change is stacked on its head
`4c45f2bd932592fa86820f2e3360085f9e060c38`; it removes duplicate generic
left proofs and retains the right action and actual Ell-circular readouts.
The new owner under the requested title has the specific scope in this table.

## Operator and incidence calculation

Write `N` for the native split norm. Kirmse contraction supplies both orders
of the identities

`L_conj(X) L_X = N(X) I` and `R_conj(X) R_X = N(X) I`.

When `N(X) ≠ 0`, the reciprocal-norm conjugate operator is an explicit
two-sided inverse. Conversely, surjectivity would put `1` in the image.
Multiplicativity of `N` makes this impossible when `N(X)=0`, because `N(1)=1`.
This argument includes the zero element, nonzero null elements, and negative
nonzero norms.

The new phase element is the inverse Ell-coordinate image of
`positiveCircularEmbedding x + negativeCircularEmbedding p`. The already
established transported quadratic gives

`N(phaseVector x p) = x₀p₀ - x₁p₁ - x₂p₂ - x₃p₃`.

The diagonal `p=x` is Lorentzian. The doubled eight-dimensional quadratic
space is split `(4,4)`. These are different spaces. The coordinate-conjugation
and matrix algebra equivalences preserve units, giving the matrix singularity
criterion without a determinant expansion. The change does not prove the
stronger numerical formula `det(L_X)=N(X)^4`.

For the convention `[a,b,c]=(ab)c-a(bc)`, the left-composition discrepancy
`(L_a L_b-L_(ab))(c)` equals `-[a,b,c]`. The existing Furey operator-lift owner
also treats mixed left/right commutators; these are different operator
expressions and must retain their displayed argument orders.

An isotropic element need not be square-zero: the pole idempotents are
nonzero null elements. Square-zero conclusions require the actual
trace-zero/imaginary or square-zero hypotheses. If a square-zero element is
zero, its nilpotency index is not two. Projective incidence additionally
requires nonzero point and hyperplane representatives.

## Corrected Souriau fragments

For an alternating bilinear form `B`, define

`Ω((x,ν),(y,μ)) = μ(x) - ν(y) + B(x,y)`.

The native linear graph `Γ_t(x)=(x,t B(x,·))` satisfies

`Γ_t* Ω = (1 - 2t) B`.

Thus the positive graph gives `-B`, and the negative graph gives `3B`. With
the area form on `ℝ²` and its two coordinate vectors, the negative graph
evaluates to `3`, whereas the rejected formula evaluates to `-1`. This is
recorded in `negativeGraph_plane_counterexample`. Merely imposing Jacobi or
a Lie-cocycle condition cannot fix that sign: the mathematical counterexample
also works with the abelian bracket and zero base covector.

The new affine owner constructs a native groupoid from the existing cocycle
datum. An arrow exists from `μ` to `ν` exactly when some group element sends
`μ` to `ν`. Its invariant-function consumer explicitly assumes invariance.
No entropy definition, smooth cotangent bundle, closed differential form,
or multiplicative symplectic-groupoid structure is inferred.

For `Z(e)=Σᵢ exp(-eᵢ)`, the new statistical owner specializes the existing
`logSumExp` rather than introducing another statistical family. It establishes
the midpoint inequality for `Φ=-log Z` and the transformation
`Φ(e∘σ-c)=Φ(e)-c`. Nonemptiness is substantive: the arbitrary-shift law does
not hold for an empty sum. With one state, `Φ` is exactly that state's energy,
so unconditional strict concavity would be false. The scalar shift is not
identified with a group cocycle by its name.

## Primary-source literature map

The following are related mathematical constructions and physical models,
not equivalences proved by the new owners.

| Source | Exact pointer and supported connection | Qualification |
|---|---|---|
| Chernousov, Elduque, Knus, Tignol, *Algebraic Groups of Type D₄, Triality, and Composition Algebras* (2013) | [Author manuscript](https://people.math.ethz.ch/~knus/papers/Documenta_17.pdf), §5 equations (5.1)–(5.3), and Proposition 4.6 | Zorn multiplication, hyperbolic multiplicative norm, and the related-triple triality construction. Triality requires that construction, not just dimensions. |
| Furey, *Charge quantization from a number operator* | [arXiv:1603.04078v2](https://arxiv.org/html/1603.04078v2), “Minimal left ideals,” equations (10)–(13) | Complex octonionic operators realize complex `Cl(6)` and its minimal ideals. A real pole projector is not automatically the paper's Clifford vacuum. |
| Krasnov, *Spin(11,3), particles and octonions* | [arXiv:2104.01786v1](https://arxiv.org/html/2104.01786v1), §3.2 equations (32)–(33); Theorem 1 and Remarks 2–3 | Explicit real `8 × 8` split-octonion Clifford relations. The larger semispinor constructions use tensor-product carriers of real dimension 64. |
| Todorov and Dubois-Violette, *Deducing the symmetry of the standard model from the automorphism and structure groups of the exceptional Jordan algebra* | [arXiv:1806.09450v1](https://arxiv.org/html/1806.09450v1), §4 equations (4.3)–(4.4) | The specified subgroup intersection belongs to the Euclidean Albert-algebra construction. An arbitrary real split Zorn or special Jordan identity does not supply it. |
| Gogberashvili and Gurchumelia, *Dirac and Maxwell systems in split octonions* | [arXiv:2012.02255v3](https://arxiv.org/html/2012.02255v3), §§2, 5, 7–9 | Full `Cl(4,4)` uses `16 × 16` matrices; chiral pieces have dimension eight. Their free Dirac and dyonic Maxwell reductions use specified Lagrangians and differential operators with a four-dimensional restriction. |
| Finster, Gresnigt, Isidro, Marcianò, Paganini, and Singh, *Causal Fermion Systems and Octonions* | [arXiv:2403.00360v2](https://arxiv.org/html/2403.00360v2), §2.3, footnote 1; §4.1.3 | The displayed projectors are in complex octonions. Split octonions are mentioned as another projector-bearing option. The concrete comparison associates vacuum sectors with octonion directions. |
| Freidel, Leigh, Minic, *Born Reciprocity in String Theory and the Nature of Spacetime* | [arXiv:1307.7080v1](https://arxiv.org/html/1307.7080v1), “Born Geometry and bi-Lagrangians” | Born geometry includes a symplectic form and compatible metric/endomorphism data. A neutral quadratic pairing alone does not establish those structures. |
| Blunck, Knarr, Stroppel, Stroppel, *Clifford parallelisms defined by octonions* (2017) | [Author manuscript](https://www.f08.uni-stuttgart.de/.content/media/downloads/Mathematik/mathematische_berichte/2017/2017-006.pdf), §5 and Theorem 8.1(f)–(h) | The triality comparison involves the norm quadric and its two maximal-isotropic families. The theorem starts with an octonion division algebra over a field and a quadratic extension splitting it; it is not directly a theorem about the real split carrier used here. |
| Neeb, *A classification of coadjoint orbits carrying Gibbs ensembles* | [arXiv:2601.04934v1](https://arxiv.org/html/2601.04934v1), Proposition 2.4, Theorem 2.5, §5 | With `Z=∫exp(-H)`, `Q=-d log Z` and the Fisher form is `Hess(log Z)=-dQ`. Degenerate directions are constant on the support; inverse and global image statements need the stated quotient/domain hypotheses. |

The Clifford convention here counts generators squaring to `+1` first.
The existing dimension obstruction suffices to reject a faithful full
`Cl(4,3)` embedding in `M₈(ℝ)`. An isomorphism with a particular simple
quotient or with the even algebra is not proved by this change.

For the real split carrier here, the projective null quadric is a smooth
quadratic hypersurface in `RP⁷`, hence has dimension six. This is the direct
dimension calculation for a nondegenerate real form of signature `(4,4)`,
not a specialization of the cited division-algebra theorem or a new Lean
projective-quadric construction in this change. It must be distinguished from the
imaginary-subspace quadric in `RP⁶` and the four-dimensional Klein quadric in
`RP⁵`. Likewise, an eight-dimensional chiral module is not a faithful module
for the full 256-dimensional `Cl(4,4)` algebra.

The attachment's Barbaresco slide numbers 70, 76, and 90 do not uniquely
identify a slide deck. Their specific attribution remains unverified.
The narrative's numbered sections also have no supplied source document.

## Practical value

The new algebraic results provide reusable inverse operators, a precise
singularity test for the phase pairing, typed affine-orbit arrows, and
sign-sensitive bilinear/statistical identities. They make subsequent
representation, geometric, and field-theoretic work easier to state and audit.
Physical dynamics, symmetry-breaking data, quantization, and comparisons
between the cited models remain additional mathematical constructions.
