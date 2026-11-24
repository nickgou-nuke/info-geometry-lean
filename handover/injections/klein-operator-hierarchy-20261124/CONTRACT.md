# Klein operator hierarchy: theorem contract

Continuation of draft PR #446 at `98587ebd1e5194d43753b55f1501c57f1478a11c`.
The intake is preserved in `INTAKE.md`. This contract records mathematical
targets and source-reviewed dependencies; it does not claim native compilation.

## Carriers and conventions

All geometric dimension claims here are over the real numbers. The genuine
Zorn multiplication is retained, including its cross-product terms. Its norm
is `a*b - dot v w`, of signature (4,4). A scalar extension to complex numbers
is not a proof about the real sixteen-dimensional spinor carrier.

`InfoGeometry.Algebra.ZornVectorMatrix` is the real eight-dimensional carrier
used by PR #446. `InfoGeometry.Canonical.ZornMatrix ℝ` is the real specialization
of the existing polymorphic canonical Zorn carrier. Compatibility between
these carriers must use the existing explicit linear/multiplication bridge,
never their similar names.

The Clifford relation convention is gamma(x)^2 = N(x) I. Write
P(x,y) = N(x+y)-N(x)-N(y) for Mathlib's unhalved polar form and B=P/2
for the associated symmetric bilinear form. For beta(x,y)=[gamma(x),gamma(y)]/2,
the normalization is

    [beta(x,y),gamma(z)] = gamma(P(y,z) x - P(x,z) y)
                        = 2 B(y,z) gamma(x) - 2 B(x,z) gamma(y).

This differs by a sign from the previously used seven-imaginary-generator
Clifford form -N of signature (4,3). The counterexamples below use P, not B.

## Normalized claim ledger

| Intake claim | Exact disposition |
| --- | --- |
| Cl(4,4) = End(O_s) | False: real dimensions 256 and 64. The appropriate full spinor carrier is O_s × O_s, dimension 16. A representation and equal dimensions alone do not prove an algebra isomorphism. |
| O_s = V4 ⊕ V4* are the two half-spinor modules | Conflation: this is a chosen Witt splitting of the eight-dimensional vector carrier. Each half-spinor module for Spin(4,4) has dimension 8. |
| Arbitrary L_x is a grade-one Clifford operator | False for the norm N. Use gamma(x)(s,t)=(x*t,conj(x)*s), a genuine off-diagonal 16D operator, with its existing native Clifford lift. |
| Grade-one and grade-two parity | Prove that gamma(x) anticommutes with chirality C(s,t)=(s,-t), and that antisymmetrized products commute with C. Do not identify C with an oriented volume product without proving that product and fixing the orientation. |
| Clifford grade k | The natural algebra grading is Z/2. Integer exterior grades need the exterior/Chevalley identification; Clifford multiplication mixes integer grades. |
| Bivectors act by infinitesimal orthogonal transformations | Use half-commutators of gamma operators and derive their commutator action on gamma(z), with all factors of 2 explicit. A connection is an additional Lie-algebra-valued 1-form; curvature is a Lie-algebra-valued 2-form. |
| N(x)=0 gives kernel dimension 4 | Require x≠0. For x=0 the kernel is all 8D. Target the full-carrier left kernel, not just the existing imaginary right-kernel theorem. |
| Multiplication incidence equals scalar orthogonality | False in both directions on the full carrier: E11²=E11 with polar(E11,E11)=0; E11*E22=0 with polar(E11,E22)=1. |
| A left kernel is a null 4-plane | Prove N(y)=0 for every member, dimension 4, and maximality among norm-null linear subspaces. Internal polar vanishing follows by polarization. This does not assert that every product of two kernel members vanishes. |
| G2 covariance preserves incidence | An actual invertible linear multiplication automorphism transports ker L_x to ker L_(g x). Infinitesimally, reuse the genuine derivation identity [D,L_x]=L_(D x). |
| The derivation algebra has dimension 14 | Reuse the existing real 14-parameter linear equivalence and finrank theorem after inspecting their hypotheses; no group-level split-G2 classification follows from dimension alone. |
| Spin and multiplication automorphisms are interchangeable | Spin preserves the quadratic/triality structure through its appropriate representations. A common action preserving octonion multiplication is an additional condition. Automorphisms fix the unit and trace, so their orbits are not automatically the whole full-null quadric. |
| Full null quadric, Klein quadric, split Cayley hexagon | Distinct geometries. The full norm-null projective quadric has dimension 6. The classical Klein quadric for lines in projective 3-space has dimension 4 and lies in projective 5-space. The split-Cayley hexagon uses the imaginary octonion space and an additional multiplication incidence condition. |
| Triality permutes vector, spinor, and gauge-flux representations | False as stated: D4 triality permutes the vector and the two half-spinor 8D representations. Its adjoint action transforms the 28D Lie algebra; it does not turn that module into an 8D module. |
| All primitive types live on one homogeneous space G/H | A group action and a specific stabilizer are required for each orbit type. Null rays and the two families of maximal isotropic planes have different parabolic stabilizers. |
| Souriau action groupoid already is T*G ⇒ g* | Not established by PR #446: that owner is an algebraic action groupoid. A cotangent symplectic groupoid needs the smooth cotangent construction, groupoid maps, symplectic form, and compatibility proofs. Its Poisson symplectic leaves are connected coadjoint orbits, or connected components of orbits for a disconnected group, in the base g*. |
| Casimirs classify all orbits and physical labels | Overstrong without a specified group and orbit class. No general orbit-separation or mass/spin/helicity classification is asserted. An outer automorphism can permute invariant polynomials; covariance does not mean it fixes every invariant value. |

## Existing owners and exact reuse

- `Canonical/ZornCliffordRepresentation.lean` constructs the quadratic form,
  the doubled gamma action, its Clifford square relation, the native
  `CliffordAlgebra.lift`, and restriction to Mathlib's spin group.
- `Algebra/ZornLeftDeterminant.lean` in PR #446 constructs the actual 8×8
  left-action matrix and its linear-action bridge before its determinant proof.
- `Lie/SplitOctonionAnnihilatorDimension.lean` proves a full 8D **right** kernel
  has dimension 4 for a nonzero **imaginary** null input; its imaginary slice
  has dimension 3. These hypotheses do not prove the proposed full-left target.
- The genuine real derivation and automorphism owners are selected by their
  source declarations. A file bearing “G2” or “isomorphism” in its name does
  not supply a group classification or an algebra equivalence.
- `Canonical/SplitOctonionAutomorphismCore.lean` defines the actual subgroup
  of invertible real linear maps preserving multiplication and the unit.
  `Lie/CanonicalZornRegularDerivation.lean` proves the existing commutator
  identity from the Leibniz law. `Lie/CanonicalZornDerivationDimension.lean`
  constructs the fourteen-parameter derivation equivalence and its dimension.
  The new covariance owner does not assume either covariance conclusion as
  a field of a new structure: it restricts the existing maps to real kernels.
- `Canonical/CanonicalZornCliffordIsomorphism.lean` concerns a complex carrier
  and explicitly stops at prerequisites; it is not a real Clifford isomorphism.

## Causal proof order

1. Reuse the real Zorn additive/module structure, bilinear multiplication,
   conjugation, norm composition, and Kirmse contractions.
2. Construct/identify the actual left multiplication linear map and its matrix.
3. Bound dimensions of norm-null submodules by an explicit real positive
   projection; show both image and kernel are norm-null under their exact
   hypotheses; use rank-nullity to obtain dimension 4 and maximality.
4. Use multiplicative linear equivalences to transport product-zero incidence
   and kernels. Reuse derivation covariance for the infinitesimal version.
5. Reuse the doubled Clifford action; establish real dimension certificates,
   chirality parity, and bivector commutator covariance on that actual carrier.
6. Keep unconstructed projective quotients, homogeneous spaces, full triality
   identifications, Lie-group classifications, and smooth symplectic groupoids
   as explicit open work rather than hidden assumptions in accepted theorems.

## Fixed source orientation

The separate volume owner uses the exact order (1,q1,q2,q3,q4,q5,q6,q7),
where qi=Vi-Ui for i=1,2,3, q(i+3)=Ui+Vi, and q7=E22-E11. It defines that
product inside the native Clifford algebra, then proves its represented
operator is minus C, where C(s,t)=(s,-t), by reusing the previous exact
seven-operator volume. The represented volume squares to the identity;
negating the source volume gives the selected chirality convention.

This is a theorem about the specified product and its operator image. It
does not establish an exterior-degree-eight identity or infer a native
Clifford-element square from an operator square without injectivity.

## Acceptance boundary

Complete proof terms without `sorry`, `admit`, custom axioms, `native_decide`,
or scalar replacements are required. Source review, native elaboration,
declaration axiom audit, and full-repository checks are separate results.
The prior draft's incomplete validation remains incomplete until actually run.
No change to dependency pins, the compiler, maintained gates, or another
workspace's build/cache ownership is authorized by this mathematical extension.

## Primary mathematical references

These references support the mathematical interpretation. They do not replace
native elaboration or axiom auditing of the Lean sources.

- Elman, Karpenko, Merkurjev, *The Algebraic and Geometric Theory of Quadratic
  Forms*, Example 11.5: hyperbolic Clifford algebra as endomorphisms of the
  exterior module, with its even/odd block decomposition.
  https://www.math.ucla.edu/~rse/book/Kniga.pdf
- Manivel, *BRIDGES Lectures: G2 in action*, section 2.3: full composition-algebra
  annihilators and maximal isotropy. The Lean target includes the explicit
  nonzero assumption used in the mathematical argument.
  https://arxiv.org/abs/2508.12757
- Baez and Huerta, *G2 and the Rolling Ball*: imaginary split-octonion
  incidence, distinct null/zero-product conditions, and the three-dimensional
  imaginary annihilator.
  https://arxiv.org/abs/1205.2447
- Ishikawa, Machida, Takahashi, *Geometry of D4 conformal triality and
  singularities of tangent surfaces*: the three different homogeneous
  spaces in the real D4 incidence geometry.
  https://journalofsing.org/volume12/ishikawa-machida-takahashi.pdf
- Rudnev and Selig, *On the use of Klein quadric for geometric incidence
  problems in two dimensions*: the classical Klein quadric in projective
  five-space.
  https://arxiv.org/abs/1412.2909
- Mikosz and Weber, *Triality, characteristic classes, D4 and G2
  singularities*, sections 7.2–7.3: split triality and the fixed split-G2 algebra.
  Its invariant-polynomial discussion also distinguishes covariance from
  pointwise invariance.
  https://arxiv.org/abs/1311.0507
- Crooks and Mayrand, *Symplectic reduction along a submanifold*, section 4.1:
  the cotangent symplectic groupoid and the Poisson structure on its base.
  https://www.cambridge.org/core/journals/compositio-mathematica/article/symplectic-reduction-along-a-submanifold/9E17032854939CB7FC79521E367894FD
