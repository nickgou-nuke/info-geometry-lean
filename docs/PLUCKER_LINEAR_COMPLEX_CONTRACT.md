# Plücker complexes and Peirce brackets: theorem contract

## Source, intent, and recovery status

This development formalizes the mathematical claims extracted from the supplied
Plücker material and supplementary operator-ring draft. The sources reviewed in
the original work were the 378-page supplied republication `Liniengeometriev1.pdf`
of Julius Plücker's *Neue Geometrie des Raumes* (1868), and the supplementary text
covering pencils, quadratic complexes, polar systems, and Peirce brackets. The
recorded source anchors are §1, nos. 26–27, PDF pp. 45–46 for linear complexes;
no. 45, pp. 65–67, equations 1.89–1.91 for special complexes; nos. 60–61,
pp. 80–81 for pencils; and nos. 308–309, pp. 289–290 for quadratic polar systems.
These page anchors come from the earlier source review and were not rechecked
against the PDF during recovery. No source PDF or long transcription is included
in this change.

The five mathematical owners use existing repository structures and genuine
Mathlib linear maps, bilinear forms, quadratic forms, matrices, and exterior
powers. They separate assumptions needed for geometry from polynomial identities
and preserve multiplication order in the noncommutative statements.

The six Lean files, including the Audit, were recovered on 11 November 2026.
Their SHA-256 values match those recorded for the successful independent
verification on 10 November. This contract and the supporting configuration were
reconstructed separately and are not claimed to be byte-identical to their
earlier copies. The manifest's nine package revisions match the exact baseline
manifest. Recovery included checksum and static configuration checks; it did not
include another Lean/Lake compilation. The original raw QA logs and full
69-entry hash inventory remain unavailable.

| Component | Fixed reference |
|---|---|
| Repository | `nickgou-nuke/info-geometry-lean` |
| Historical verification baseline | `732d97c30f292d61ea332ca9da4d1e1d8f69bd00` |
| Lean toolchain | `leanprover/lean4:v4.34.1` |
| Observed Lean compiler commit in historical QA | `5045d0056413266e57c625dcd7c365b10e377c52` |
| Mathlib revision | `d13f23b723b8a846827a245b89c10fc7d3f11612` |

## Existing owners reused

| Existing owner | Role in the development |
|---|---|
| `Canonical/PfaffianFour` | Four-dimensional alternating matrix and Pfaffian-square determinant identity. |
| `Projective/KleinQuadric` | Existing `Plucker6`, Klein quadratic, polar form, scaling, and pencil identities. |
| `Projective/KleinQuadricIncidence` | Six-coordinate incidence pairing. |
| `Projective/ExteriorKleinCoordinateIncidence` | Compatibility of row determinants with Plücker incidence. |
| `Projective/ExteriorPowerPluckerBridge` | Real decomposability converse for the Klein equation. |
| `Projective/ExteriorKleinTwoPlaneQuotient` and its existing correspondence modules | Actual rank-two submodules, nondegenerate frames, and their projective Klein correspondence. |
| `Projective/ExteriorKleinNullTwistor` | Native Klein quadratic form on the literal exterior square and its projective null locus. |
| `OperatorAlgebra/PeirceSpine/ThreeHorizonHodgeDecompositionPoset` and its imports | Complementary idempotent, orthogonal corners, and ordered corner-composition lemmas. |

This change adds no parallel definition of the existing projective line space,
Klein equation, or Peirce corner algebra.

## Carriers and coordinate conventions

The established six-coordinate order is

```text
(p01, p02, p03, p12, p13, p23),
K(P) = p01*p23 - p02*p13 + p03*p12.
```

The parameter `C : Plucker6 R` is a polar representative. The linear equation on
a line `P` is `incidenceForm C P = 0`. Its raw coefficient tuple, in the order
displayed above, is

```text
(C.p23, -C.p13, C.p12, C.p03, -C.p02, C.p01).
```

Consequently the native alternating matrix is

```lean
skew4 C.p23 (-C.p13) C.p12 C.p03 (-C.p02) C.p01
```

For the source's anonymous-index ordering `(x,y,z,τ)`, the six ray coordinates
used in the linear equation are `(p03,p13,p23,p12,-p02,p01)`. Raw coefficients
`(A,B,C,D,E,F)` therefore correspond to polar coordinates `(C,-B,D,A,E,F)`,
whose Klein value is `A*D + B*E + C*F`. If the names are instead identified
literally with the repository's `(t,x,y,z)`, with `t = τ`, the permutation gives
polar coordinates `(D,E,F,-C,B,-A)`, and the Klein value changes sign. Its square
and zero condition are unchanged. No metric or physical interpretation follows
from choosing either coordinate convention.

Polynomial identities and alternation are established over `CommRing`. The
nondegeneracy and hyperplane results assume `Field`. The intrinsic two-plane,
decomposability, and quadratic-complex developments use the repository's real
four-space and exterior square. The general Peirce and matrix-unit identities
need only `Ring`; only their scalar Klein specialization uses `CommRing`.

## Causal order of the formal development

1. Define `complexMatrix C` using the existing `skew4`, and `complexForm C` as
   the genuine Mathlib bilinear form obtained by `Matrix.toBilin'`.
2. Derive `det (complexMatrix C) = K(C)^2` from the established Pfaffian theorem.
   Prove alternation directly, including characteristic two.
3. Over a field, prove that `complexForm C` is nondegenerate exactly when
   `K(C) ≠ 0`. A nonzero point then defines a nonzero covector whose kernel has
   vector-space dimension three. Alternation puts the point in its own kernel.
   Nonzero rescaling of either point or complex representative preserves that
   polar submodule.
4. Transport the form to the existing `Vec4`, and prove its evaluation is exactly
   the existing incidence pairing with `linePlucker x y`.
5. Define `lineComplex C` as a set of actual `RealTwoPlane` values by vanishing
   of the restricted bilinear form. Prove that testing a nondegenerate frame pair
   tests the entire restriction.
6. For a representative `linePlucker u v`, identify complex membership with
   projective incidence with the directrix spanned by `u,v`.
7. Prove the exact radical equality. If a vector lies outside the directrix,
   extend the independent frame to produce a nonzero four-vector exterior
   product and hence a nonzero determinant functional. This proves the reverse
   inclusion as well as the immediate forward inclusion. The radical has
   dimension exactly two.
8. Use the existing full real Plücker converse to obtain a nondegenerate frame
   for every nonzero special representative. The Lean hypothesis is explicitly
   `complexMatrix C ≠ 0` together with `K(C) = 0`. The resulting directrix is
   exactly the radical, and its incident lines are exactly `lineComplex C`.
   For frame representatives, a point's polar covector has kernel equal to the
   whole four-space exactly when the point lies on that directrix.
9. Introduce homogeneous pencil parameters `(s,t)` and prove
   `K(sC+tD) = s^2*K(C) + s*t*polar(C,D) + t^2*K(D)`. All common lines of the
   generators lie in every member; replacing the second generator by a member
   with `t ≠ 0` preserves their intersection. Every nonzero real special member
   has a directrix meeting those common lines. Existence or number of real roots
   is not assumed.
10. Define a quadratic complex from a native
    `QuadraticForm ℝ ExteriorSquare`, restricted to the existing projective
    `KleinLocus`. Prove that adding a scalar multiple of the Klein quadratic
    preserves the resulting set of projective lines.
11. Define the draft's chosen polar normalization as `associated Q` plus a
    scalar multiple of the full Klein polar form. Prove symmetry, the exact
    diagonal formula `Q(X) + 2*a*K(X)`, and the equivalence of self-incidence
    with `Q(X) = 0` on the Klein cone.
12. Independently use the existing Peirce corner algebra to prove ordered
    two-step multiplication and its commutator. Realize the pattern explicitly
    by `step r ρ = Matrix.single 0 1 r + Matrix.single 1 2 ρ`, then specialize
    the resulting coefficient identity to scalar Klein coordinates.

The owners expose 47 public declarations: nine definitions and 38 theorems.

| New owner | Public declarations |
|---|---:|
| `PluckerLinearComplex` | 13 |
| `PluckerLinearComplexGeometry` | 14 |
| `PluckerComplexPencil` | 7 |
| `PluckerQuadraticComplex` | 7 |
| `PluckerPeirceBracket` | 6 |

## Ordered Peirce statement

Let `P1` and `P2` be idempotents in an associative ring, with
`P1*P2 = 0 = P2*P1`, and let `P0 = 1 - P1 - P2`. The proven product is

```text
(P1*r*P0 + P0*ρ*P2) * (P1*s*P0 + P0*σ*P2)
  = P1*(r*P0*σ)*P2.
```

The commutator is therefore

```text
P1*(r*P0*σ - s*P0*ρ)*P2.
```

The middle projector remains in both ordered paths. Replacing arbitrary ring
inputs by central scalar multiples of the identity would annihilate the
off-diagonal corners, so it does not provide the intended nontrivial scalar
model. The explicit matrix-unit model supplies that realization:

```text
[step r ρ, step s σ] = Matrix.single 0 2 (r*σ - s*ρ).
```

For the source's assignment

```text
(r,s,h,σ,ρ,η) = (P.p03,P.p13,P.p23,-P.p12,-P.p02,P.p01),
```

the Klein equation gives coefficient `h*η`, namely

```text
[step P.p03 (-P.p02), step P.p13 (-P.p12)]
  = Matrix.single 0 2 (P.p23*P.p01).
```

This is a proved compatibility formula for the displayed map. It does not assert
that arbitrary Peirce corners are one-dimensional or canonically identifiable
with the six scalar coordinates.

## Corrections to the supplementary draft

| Draft claim or ambiguity | Formal statement and correction |
|---|---|
| Every point has a polar plane. | A nonzero point in a nonspecial complex has a three-dimensional vector hyperplane. On a special directrix the polar covector is zero and its kernel is the entire four-space. |
| A pencil always supplies two real directrices. | The theorem is conditional on a nonzero real special member. Homogeneous parameters include infinity; real roots need not exist. The earlier source review recorded that p. 81 permits imaginary directrices. |
| A quadratic coefficient record has “20 fields.” | The draft record actually contains 21 scalar coefficients. The implementation uses a native quadratic form and proves the Klein ambiguity directly. No coefficient-count theorem is asserted. |
| A polar multiplier or its normalization is unique. | The chosen associated/full-polar convention has diagonal `Q + 2*a*K`. Its zero condition on the Klein cone is independent of `a`; uniqueness of the multiplier is not claimed. |
| Six arbitrary Peirce corners are six scalar Plücker coordinates. | General corners can be arbitrary additive groups/modules. The code supplies a concrete matrix coefficient map, not a universal isomorphism. |
| The sum of null elements must be non-null. | The mixed polar term may vanish. The homogeneous quadratic identity retains that term and does not force it to be nonzero. |
| A single parameter count applies without quotient conventions. | The explanatory count is 21 coefficients, then 20 after quotienting by the Klein equation, then 19 projectively. The earlier source review recorded the 19/20 distinction on p. 290. These dimension counts are not new formal theorems here. |
| The expanded quadratic source formula fixes every sign unambiguously. | The earlier comparison found opposite signs for the `S*s*σ` term on pp. 156 and 283. The native quadratic-form construction does not depend on choosing that disputed expansion. |

The exact source-coordinate conversions above must accompany any use of the
coefficient identities. Renaming spatial coordinates without applying the
permutation and signs changes the displayed formulas.

## Scope and boundary cases

The zero tuple defines the identically zero complex form and contains every
line. It is excluded from the special-directrix classification by the nonzero
matrix hypothesis. A point on a special directrix has no unique projective polar
plane determined by its zero covector; this agrees with the exceptional case
recorded on source p. 66. Projective incidence includes intersection at infinity.

This change does not construct a scheme-theoretic Grassmannian, classify Kummer
surfaces, prove a Plücker isomorphism over a noncommutative base, add a topological
completion, or derive physical dynamics. It makes no E8, Majorana, rotating-ball,
or pitch-as-anticommutator claim. An individual off-diagonal Peirce corner is
square-zero under the stated orthogonality, while a sum with a composable corner
need not be square-zero; the ordered product theorem exhibits the surviving
term.

## Verification and reproduction

The earlier independent verification finished on 10 November 2026 at
18:31:52.782520 UTC (20:31:52 in Sofia). The complete focused Lake target returned
exit code zero with `Build completed successfully (8981 jobs).` This is the
reported job count, not a claim that every dependency was rebuilt from scratch.
A separate fresh Audit elaboration, using its absolute source path, also
returned exit code zero.

That Audit covered all 47 public declarations exactly once and compiled four
boundary examples: characteristic-two nondegeneracy, the zero form, a real
finite pencil with discriminant `1 + μ^2`, and its member at infinity. The
observed aggregate axiom set was exactly
`{propext, Classical.choice, Quot.sound}`. The two general Peirce product and
commutator theorems used only `propext`; this smaller set is not attributed to
the other declarations.

Historical QA also recorded the actual compiler commit, all nine pinned package
revisions with clean dependency checkouts, and unchanged before/after hashes for
69 files: 58 repository Lean sources, ten configuration/helper files, and the QA
runner. The shared repository build lock was used. The complete raw inventory
and logs have not been recovered, so today's check establishes exact byte
identity for the six recovered Lean files only, not for that entire historical
environment or import closure.

The historical strict OpenGauss screen reported zero traps across all six
files. A separate semantic-vacuity invocation with `--fail-on warning` returned
exit code one for one reviewed `trivial_surface` warning at `step_mul`, whose
short proof applies substantive matrix-unit multiplication lemmas with `simp`.
That invocation did not pass its warning threshold, and the development is not
described as warning-free.

From a checkout containing this development, run from the repository root:

```sh
python3 verification/plucker-complex/check.py exe cache get
python3 verification/plucker-complex/check.py build
python3 verification/plucker-complex/check.py env lean \
  lean/InfoGeometry/Projective/PluckerLinearComplexAudit.lean
```

The cache command is needed when the pinned artifacts are absent. These commands
do not run `lake update`. The wrapper uses the existing shared build lock,
validates the root and focused workspace metadata, and runs Lake with the
repository root as its current working directory. Therefore the Audit path
above is repository-relative: `lake -d` does not relocate that working directory
in the pinned version. The historical independent Audit used an absolute path
and was unaffected by the earlier relative-path error corrected in the restored
README and workflow.

The focused package uses the parent repository's sources and normal
`.lake/packages` dependency directory. It requires the repository's existing
mathematical owners and build-lock helpers; the focused package is not a
standalone project.

The historical root-package attempt stopped before elaboration because the
optional `HomotopyHypothesis` dependency was unavailable; preflight also recorded
`Atlas` and `GIFT` issues, with no recoverable pins for the first two. No unpinned
dependency was installed and no publication gate was bypassed. A focused pass
does not establish successful integration of unrelated root default targets.

During recovery on 11 November 2026, the GitHub workflow received static checks
of its syntax, embedded Python, and paths. No GitHub Actions run was performed
as part of that recovery. Subsequent remote verification is recorded in the
associated pull request's checks and artifacts.
