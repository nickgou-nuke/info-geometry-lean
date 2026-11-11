# Twistor null planes and self-adjoint projectors

## Intake and disposition

The source is the Bulgarian mathematical intake supplied on 2026-11-11 after
creation of [PR #306](https://github.com/nickgou-nuke/info-geometry-lean/pull/306).
Its prose is preserved in
[the intake transcription](TWISTOR_NULL_PROJECTOR_INTAKE_BG.md),
with Markdown table whitespace normalized. Statements in that transcription
are input claims, not accepted mathematical results.

This development addresses the claimed identification of a real spacetime
incidence plane with a self-adjoint rank-two projector for the Penrose form.
The correct conclusion is an obstruction: a self-adjoint idempotent with
totally isotropic image is zero. A nonzero oblique projector onto the same
plane does exist, and the implementation constructs it explicitly.

Scope: algebraic linear maps and finite complex incidence submodules. Risk
class R2 for reuse of existing owner structures; physical interpretations and
global geometric identifications remain outside the theorem contract.

This contract records source reviews and native results at their exact
revisions. Root integration remains incomplete. The current checks and body
of [PR #307](https://github.com/nickgou-nuke/info-geometry-lean/pull/307) report
the latest native outcome; an earlier run is not a certificate for later bytes.

## Claim ledger

| Intake claim | Mathematical disposition | Repository treatment |
|---|---|---|
| Projective lines in `P(V)` correspond to two-dimensional subspaces and decomposable bivector rays | Valid with a specified field and nonzero, independent generators | Reuse the existing Plücker/exterior owners; PR #306 concerns the exterior-square action, not this projector obstruction |
| One twistor determines a twistor line | False without additional incidence data | A nonzero twistor gives a projective point; a two-plane gives a projective line |
| All of `Gr(2,4)` is real Minkowski spacetime and also its null rays | Conflates complex geometry, reality conditions, and different dimensions | Keep complex compactified spacetime, its Lorentzian real slice, and null projective twistors distinct |
| The real Klein form has interchangeable signatures `(3,3)` and `(4,2)` | False over the real numbers | The ordinary real Plücker quadric is split; the Lorentzian compactification uses a different real structure |
| An oriented Grassmannian is a future/past splitting of the Klein quadric | Unsupported identification | Real plane orientation is additional double-cover data; an ordinary projector forgets it |
| `z φ` is idempotent | Conditional on `φ(z)=1` for a nonzero dyad | Existing `RegularDyadCompression` and `RealDualTwistor` own normalized and incidence dyads |
| Independent columns make `UU†` a rank-two projector | False without orthonormality | The positive-metric formula requires `U(U†U)⁻¹U†`; this formula is explanatory, not implemented here |
| The Penrose twistor bra normalizes every nonzero twistor | False for null vectors | A null self-pairing remains zero under rescaling |
| A nonzero totally null plane is the image of a self-adjoint idempotent for the same form | False | The new generic obstruction and Penrose specialization address exactly this claim |
| A nonzero totally null plane admits no idempotent at all | Also false | Construct a nonzero oblique idempotent with exactly that image and complex rank two |
| Weights or spinor components automatically supply physical mass | Additional definitions and dynamics required | No mass theorem is claimed; rescaling a projector is generally not idempotent |
| Rank-one projectors are elements of the polynomial Weyl algebra | False in characteristic zero | Its domain property rules out nontrivial ring-element idempotents; operator completions and matrix idempotents are separate constructions |
| Four twistor coordinates imply a finite-dimensional CCR representation | False for nonzero Planck parameter in characteristic zero | The trace of a finite-dimensional commutator is zero; no CCR representation is constructed here |
| Differentiating rank `k` intrinsically requires rank `k+1` | Confuses rank, exterior degree, and form degree | Reuse existing idempotent tangent owners; no rank tower is asserted |
| Ambient Maurer–Cartan flatness forces projected curvature to vanish | False | Existing `PeirceProjectedConnection` computes actual projected curvature |
| Replacing `d` by an ordinary `[D,·]` automatically gives a differential | False | A differential calculus needs grading/quotient/domain data; no spectral triple is constructed here |
| Arbitrary projectors or Maurer–Cartan flatness directly derive Yang–Mills equations | Not established | Requires additional field, metric, integrability, and reality hypotheses |
| A `U_q(su(2,2))` action canonically fixes the proposed quantum projector | Not formulated | A deformed algebra, real form, action, projector, and equivariance law must first be specified |

## Existing owner search

The search covered related statements and alternate formulations in `lean/`,
`src/`, and the pinned Mathlib sources. This is a bounded source search, not a
claim that a runtime declaration graph or optional external index was fresh.

Relevant existing statements include:

- `Core/IdempotentTangent.lean`: `tangent_iff_diagonal_corners_zero`,
  `tangent_eq_offDiagonal`, `tangent_eq_double_commutator`, and the
  self-adjoint/skew-adjoint generator criterion over actual associative rings.
- `Canonical/TensorIdempotentTangentRange.lean`: derivation evaluation,
  the canonical inner generator, and its full tangent range in the existing
  colimit algebra. These results are not reimplemented here.
- `OperatorAlgebra/PeirceProjectedConnection.lean`: the actual projected
  connection on the Peirce range and its curvature operator.
- `LinearAlgebra/RegularDyadCompression.lean`: normalization and idempotence
  when the vector-covector pairing is nonzero.
- `Twistor/RealDualTwistor.lean`: dyad composition, square, and the nonzero
  incidence/square-zero equivalence on its real dual-pair carrier.
- `HodgeCohomology/KreinHodgeDirac.lean`: a prior real bilinear square-zero
  implication for the diagonal pairing of image vectors.
- `src/InfoGeometry/Krein/ExceptionalPointBilinear.lean`: a related real
  bilinear forward implication for pairwise image isotropy. This is a separate
  source surface, not an import used by this patch.
- `Twistor/PenroseTwistor.lean`: the actual complex carrier and diagonal
  Hermitian pairing.
- `Twistor/PerjesConventions.lean`: the signed incidence map, invertible
  Witt-to-diagonal change of frame, its factor-two pairing identity, and
  isotropy for Hermitian spacetime matrices.

The new generic converse and complex incidence application strengthen these
owners. They are not presented as the repository's first isotropy/nilpotency
result. The differently framed `TwoTwistorIncidenceIsotropy` owner is not used:
its direct diagonal equation has a different interpretation.

## Generic theorem contract

Owner: `lean/InfoGeometry/LinearAlgebra/IsotropicSelfAdjoint.lean`.

Native carriers and hypotheses:

```lean
{R V W : Type*} [CommSemiring R]
[AddCommMonoid V] [Module R V]
[AddCommMonoid W] [Module R W]
{σ : R →+* R}
(B : V →ₗ[R] V →ₛₗ[σ] W)
(hB : B.SeparatingLeft)
(P : Module.End R V)
(hself : B.IsSelfAdjoint P)
```

`square_zero_iff_image_isotropic` proves

\[
P^2=0\quad\Longleftrightarrow\quad
\forall x,y,\ B(Px,Py)=0.
\]

The identity used is `B(P(P x), y) = B(P x, P y)`, supplied by native
adjunction. The reverse implication then uses left separation of `B`.
`eq_zero_of_idempotent_of_image_isotropic` combines this result with native
`IsIdempotentElem P` to prove `P=0`.

The result assumes neither symmetry nor positivity of the form, neither
finite dimension nor a field, and no commutativity of endomorphisms.
Multiplication in `Module.End R V` is actual ordered composition. There is
no new assumption packet whose fields contain the desired conclusion.

## Concrete Penrose contract

Owner: `lean/InfoGeometry/Twistor/PenroseNullProjector.lean`.

Use the existing complex carrier `TwistorCarrier = Fin 4 → ℂ` and existing
`twistorHermitian`. This form is conjugate-linear in its first slot. Native
`IsSelfAdjoint` expects a linear first slot, so the implementation uses
`twistorHermitian.flip.IsSelfAdjoint P`. Exchanging the two quantified
variables recovers precisely the usual adjunction equation for the original
pairing; the metric is not replaced.

For `X : ComplexSpacetime = Matrix (Fin 2) (Fin 2) ℂ`, let

\[
E_X(\pi)=T(-iX\pi,\pi),
\]

where `T = wittToDiagonal` is the existing invertible complex-linear map.
The sign is the existing `paperIncidence` convention. Its exact pairing law is

\[
h(TZ,TW)=2\,h_{\mathrm{Witt}}(Z,W).
\]

`incidenceEmbedding` is the native composition defining `E_X`. The code
proves its injectivity. If `Xᴴ=X`, `incidenceEmbedding_isotropic` proves
`h(E_X π,E_X ρ)=0` by the existing incidence and change-of-frame identities.

The central specialization is:

```lean
theorem eq_zero_of_selfAdjoint_of_range_le_incidence
    (X : ComplexSpacetime) (hX : Xᴴ = X)
    (P : Module.End ℂ TwistorCarrier)
    (hP : IsIdempotentElem P)
    (hself : twistorHermitian.flip.IsSelfAdjoint P)
    (hrange : P.range ≤ (incidenceEmbedding X).range) : P = 0
```

The needed separation of the actual Penrose form is proved using the four
coordinate vectors, not assumed as an additional model field.

The constructive companion is

\[
P_X=E_X\circ\operatorname{snd}\circ T^{-1}.
\]

For every complex `X`, the implementation proves that this operator fixes
every `E_X π`, is idempotent, has range exactly `range E_X`, has complex rank
two, and is nonzero. If `Xᴴ=X`, it is not self-adjoint for the Penrose form.
This is an affine incidence-chart construction; it does not claim a global
choice of complement over compactified spacetime.

## Dependency order and scope boundary

The generic derivation is

`adjunction + separation → square-zero/isotropy equivalence → idempotent obstruction`.

The concrete derivation is

`existing incidence + actual frame change → isotropic embedded plane → obstruction`,

with the separate constructive branch

`lower-spinor retraction → graph projector → exact range + rank two + nonzero`.

Combining those branches proves failure of self-adjointness. Each arrow
denotes an actual map or theorem dependency.

The explanatory matrix calculation
`(UU†H)² = U(U†HU)U†H = 0` for a totally null frame is not a declaration in
this patch. Neither its trace-zero consequence nor the positive-metric
Gram-inverse formula is newly formalized here. The patch also does not prove
the full Grassmannian/Klein isomorphism, compactification, quantum deformation,
K-theory classification, a global flag manifold, mass, or Yang–Mills dynamics.

## Validation and integration

Pinned environment: Lean `v4.34.1`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The root toolchain, manifest, and
Lake configuration are unchanged.

The scoped verifier is
`verification/twistor-null-projector/check.py`. It uses the maintained global
build lock, copies the 14-owner repository import closure into a new regular
package, builds it without pre-existing repository oleans, checks both owner
files, and invokes the maintained complete declaration-axiom audit. Native
Mathlib artifacts may be reused only with the pinned dependency source.
This is a scoped verification target; it is not the root build gate.

Both new owners are also registered in the existing
`tools/quality/check_perjes_klein_targets.txt` selection. The existing
`perjes-klein.yml` pull-request workflow selects changes under the twistor
directory and compiles that selection with its repository dependencies.
Registration is not evidence that the workflow has run or passed.

```bash
python3 verification/twistor-null-projector/check.py --wait-for-build-lock
python3 tools/infra/opengauss_screener.py --strict \
  lean/InfoGeometry/LinearAlgebra/IsotropicSelfAdjoint.lean \
  lean/InfoGeometry/Twistor/PenroseNullProjector.lean
python3 tools/quality/proof_proxy_staged_gate.py
git diff --cached --check
```

The independent A-A source review passed for the initial frozen owner hashes
`e80a2cb4f3b8cc26b3465921aa86e3a304dfe8bdc0631646d11f3320ded01150`
and `f35536d3185ef62683f10ce80a3abbd8199d0292082ab82232d2e3cb6ec693df`.
That review is not a compiler or axiom-audit result.

Independent static QA also observed the strict source screener exit 0 with
zero traps, the nonempty staged proof gate exit 0, and the staged whitespace
check exit 0. Live and staged bytes of both Lean owners matched those hashes.
The Python verifier passed a syntax-only AST parse; its native path has not
yet executed.

The first actual [Perjes/Klein CI run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/42996946019)
passed for PR head `6058b67987cbe970bd2fea6531d469a38e087e27` and checked merge
revision `670c6766a61716a388d165655a341847ae461c6d`. Both have source tree
`ee0226cc54248a1bdbfb649c56e4c46b41dc7ce9`. Independent QA reconciled all 30
copied repository-source hashes with the exact Git blobs and checked every
compiler return code. All 30 compiled successfully.

The complete native audit covered 358 declarations owned by the ten selected
modules. Of these, the new generic owner contributes two and the Penrose
owner contributes fifteen: fourteen explicit declarations and the generated
`incidenceEmbedding._proof_1`. The generic owner uses only `propext` and
`Quot.sound`; the Penrose owner's footprint additionally includes
`Classical.choice`. No other axiom appeared. The audit itself emitted no
warning or error. These are observed native counts, distinct from the sixteen
explicit source declarations.

That successful run emitted no warning for the generic owner and one for the
Penrose owner: an unnecessary `simpa` in the final rank calculation. The
subsequent minimal correction uses the native `Module.finrank_fin_fun` lemma
directly. Its Penrose source hash is
`38db215435ac4496e938d9e0a083be9e8bec09ff825cf480fd2eaf4e5a41a745`.
Independent source reviews confirm that this changes no statement, import or
hypothesis. The earlier CI run checks the original hash, not this correction;
the later PR check must establish the result for the corrected bytes.

This observed CI run is the existing 30-owner Perjes checker, not an execution
of the new 14-owner scoped verifier. Existing imported/selected owners emitted
66 other warnings; the run is not a whole-closure zero-warning certificate.

Local Lean compilation has not executed while the maintained shared build
lock is occupied. No native result is inferred from queued preparation.
The new scoped verifier's own runtime acceptance remains pending.

The current root path preflight exits 1 because the recorded
`HomotopyHypothesis` and `Atlas` path packages are absent and the `GIFT`
gitlink is uninitialized. No substitutes or dependency-pin changes are
introduced. Root integration acceptance remains separate from scoped checks.
The [remote root build](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/42996946123)
also stopped at the missing `HomotopyHypothesis` package. Other repository-wide
checks reported archival proof debt and a pre-existing case collision between
`Physics/PellisFineStructure.lean` and `Physics/PellisfineStructure.lean`.
These files are unchanged by this PR.

## Primary mathematical references

- Stephen Huggett, [The Elements of Twistor Theory](https://people.maths.ox.ac.uk/lmason/Tws/Huggett.pdf),
  pp. 1–4: projective points, lines, the Klein quadric, real null rays, and
  real spacetime incidence.
- Tim Adamo, [Lectures on twistor theory](https://arxiv.org/abs/1712.02196),
  §§1.4, 2.1 and 4.1: incidence, reality structures, and the Ward correspondence.
- Lionel Mason, [Gravity from holomorphic discs and celestial symmetries](https://arxiv.org/abs/2212.10895),
  §2.1: the split real Klein quadric and its conformal geometry.
- Jonathan Block and Ezra Getzler,
  [Equivariant cyclic homology and equivariant differential forms](https://www.numdam.org/item/10.24033/asens.1699.pdf),
  Lemma 4.5: the Grassmannian connection and its curvature.
- Alain Connes, [Noncommutative Geometry](https://alainconnes.org/wp-content/uploads/book94bigpdf.pdf),
  Chapter VI §1: represented universal differential forms and the necessary
  quotient by the differential ideal generated by the representation kernel.
- Christian Schnell, [D-modules](https://www.math.stonybrook.edu/~cschnell/pdf/notes/d-modules.pdf),
  Proposition 2.10: the polynomial associated graded algebra of the Weyl
  algebra, from which its domain and ring-idempotent obstruction follow.

The specific projector obstruction is derived algebraically in the source;
these references justify the surrounding interpretations and distinctions.
