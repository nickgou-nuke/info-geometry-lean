# Statistical geometry: two precise boundaries

## Provenance and scope

This task extracts explicit mathematical implications from the supplied
`Pasted text(20261120-132050).txt`, SHA-256
`ad0e42944eb1e912d996e37b56add897fa0184ad8d0c294ef86a59e26ac23934`.
The intake is a literature map spanning six subjects, not an established chain
of constructions. Its historical attributions are not promoted to Lean claims.
The repository baseline is
`586c14bc9fb94eb09b56f7dc850d9d5297269f91`.

The task adds two pointwise mathematical results and one adapter to an existing
owner. It does not assert a unified manifold, supergeometry, or operator tower.
The earlier Aitchison work is separate, in PR #411.

## Bounded source and reuse ledger

The current sources were inspected after repository context preflight, including
the maintained entrypoint, graph/index, and external-reference navigation lanes.
Those indexes are navigation aids; no live-service freshness or repository-wide
proof certification is claimed.

| Intake theme | Inspected owner and reusable content | Boundary of this task |
|---|---|---|
| Dual statistical connections, Weyl geometry, and para-Kähler products | `Modular/AmariChentsovDualConnections.lean` has a positive bilinear metric, two bilinear connection maps, and a metric-duality field. `Geometry/ParaHessianMixedPotential.lean` constructs the mixed metric of a specific quadratic potential. | Prove pure-trace rigidity and give a genuine smooth divergence counterexample to global mixed nondegeneracy. No automatic identification of all three geometries. |
| Massieu and Gibbs geometry | `Thermodynamics/FiniteGibbsRelative.lean`: `relativeEntropy_eq_massieuBregman`, `relativeEntropy_nonneg`, `relativeEntropy_eq_zero_iff_common_shift`, `fisherMetric_eq_covariance`. | These are finite counting-measure exponential-family results. This task does not extend them to arbitrary reference states or noncommutative Lie-group Gibbs constructions. |
| Schur factorization and Berezinian | `Algebra/BlockSchurFactorization.lean`: ordered block factorization over a ring, ordinary determinant theorem over a commutative ring, and `scalar_schur_ratio_counterexample`. | The ordinary Schur determinant ratio is not a multiplicative Berezinian on arbitrary ordinary block matrices. Graded coefficient hypotheses must be supplied separately. |
| Super-Grassmannian charts | `SuperGrassmannian/FreeSupermoduleChart.lean`: native graded submodules, local coefficient charts, and base-change naturality. | A local algebraic chart does not construct a global supermanifold, twistor correspondence, or quantum deformation. |
| Clock/shift, color grading, and towers | `Canonical/SylvesterGrading.lean`: conditional displacement products and braiding; `Algebra/FourthRootClockShift.lean`: concrete four-state matrices; `Clifford/Cl11MarkovJonesEngine.lean`: normalized-trace compatibility under the finite binary matrix embedding. | Finite-stage compatibility does not establish a Jones basic construction, a subfactor index, or an analytic completion. |
| Roots of unity and generalized differentials | `OperatorAlgebra/InvolutiveTwistedDifferential.lean`: twisted Leibniz rule and `ringTwistedInner_square` / `twistedInner_square`; `OperatorAlgebra/PeirceSpine/CentralizerDifferential.lean`: the centralizer differential. | Reuse the existing involutive case. Bare nilpotency and a root of unity are not equivalent data; the automorphism, grading, and central-power assumptions matter. |

Paths in this table are relative to `lean/InfoGeometry/`. Inspection is source
review, not fresh compilation of all six lanes. The focused compiler closure
below includes only the actual reused dual-connection owner.

## Contract A: symmetric pure-trace rigidity

### Carrier and hypotheses

Let `V` be a real module with an additive commutative group, let
`B : LinearMap.BilinForm ℝ V` be natively nondegenerate, and let
`ω : V →ₗ[ℝ] ℝ`. Assume

\[
\omega(x)B(y,z)=\omega(y)B(x,z)\qquad\text{for all }x,y,z.
\]

No symmetry or positivity of `B` is assumed. Its left separating property is
the part of nondegeneracy used in the proof.

### Dependency order and exact targets

1. Nondegeneracy gives `ω x • y = ω y • x`.
2. If `ω x ≠ 0`, then every `y` equals `(ω y / ω x) • x`.
3. Hence `Submodule.span ℝ {x} = ⊤`; in particular, nonzero `ω` forces
   `Module.finrank ℝ V ≤ 1`.
4. If `2 ≤ Module.finrank ℝ V`, then `ω = 0`. The converse symmetry statement
   for the zero one-form is also proved.
5. Multiplication on `ℝ` with the identity one-form provides a nonzero
   one-dimensional witness, so the dimension restriction cannot be omitted.

The span results do not assume finite dimensionality. The dimension-at-least-two
corollary uses Mathlib's `finrank`; it is not presented as a theorem about every
infinite-dimensional module.

Owner: `Geometry/Statistical/StatisticalWeylRigidity.lean`.

### Adapter to the existing dual-connection model

`Geometry/Statistical/StatisticalWeylDualConnections.lean` packages the actual
`DualConnectionManifold.g` into a native bilinear form and proves both separating
conditions from the owner's positive-definiteness field. With explicit symmetry
of the first two arguments of its actual `amariCubicForm`, the factorization

\[
C(x,y,z)=\omega(x)g(y,z)
\]

and `2 ≤ Module.finrank ℝ V` force `ω = 0` and
`M.nabla_m x y = M.nabla_e x y`.

The existing structure does not contain torsion-free data or supply the needed
first-two-slot symmetry. That symmetry remains an explicit hypothesis. Its
metric-duality field is not a proof of Levi-Civita uniqueness or a construction
of a smooth manifold. The new adapter makes no such claim.

## Contract B: diagonal regularity does not imply global nondegeneracy

On the actual real line, with `s = x - y`, define

\[
D(x,y)=s^6-3s^4+3s^2
=s^2\left[\left(s^2-\frac32\right)^2+\frac34\right].
\]

Prove joint smoothness, nonnegativity, positivity away from the diagonal,
vanishing exactly on the diagonal, and vanishing of both first partial
derivatives on the diagonal. Define the mixed coefficient using nested native
Mathlib derivatives, rather than defining it to be a polynomial:

\[
H(x,y)=-\partial_x\partial_y D(x,y).
\]

Explicit `HasDerivAt` proofs then establish

\[
H(x,y)=6(5s^2-1)(s^2-1),\qquad H(x,x)=6>0,\qquad H(1,0)=0.
\]

This disproves the proposed unrestricted inference from diagonal regularity
of a divergence to nondegeneracy on the entire product. It leaves open valid
constructions on domains where the mixed Hessian is invertible.

Owner: `Geometry/DivergenceMixedHessianCounterexample.lean`.

## Source grounding

* Wong and Yang, [Pseudo-Riemannian geometry embeds information geometry in
  optimal transport](https://arxiv.org/abs/1906.00030), version 4, section 2
  and equation (15): the product construction assumes an invertible mixed
  Hessian on the chosen domain.
* Hirica, Pripoae, Pripoae, and Preda,
  [Conformal Control Tools for Statistical Manifolds and for γ-Manifolds](https://doi.org/10.3390/math10071061),
  equation (15) and Remark 7: statistical and Weyl nonmetricity impose distinct
  conditions. Contract A gives an explicit pointwise proof and records the
  dimension restriction.
* Dubois-Violette and Kerner,
  [Universal q-differential calculus and q-analog of homological algebra](https://arxiv.org/abs/q-alg/9608026),
  Example 1 and Remark 2: the twisted Leibniz condition alone does not force
  nilpotency, even at a primitive root of unity. The graded matrix construction
  includes additional hypotheses.

These sources support the stated qualifications. They do not certify every
historical priority claim in the supplied literature map.

## Validation contract and publication status

The mathematical candidates are authored separately and independently reviewed.
The coordinator performs native Lean validation after integrating the reviewed
candidates. No `sorry`, `admit`, custom axioms, `native_decide`, unsafe proof
bypasses, or replacement surrogates are accepted.

`Geometry/StatisticalGeometryBoundariesAudit.lean` audits every declaration
belonging to the three new mathematical owners and the reused dual-connection
owner, including private and generated constants. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted foundational dependencies.

`verification/statistical-geometry-boundaries/check.py` rebuilds this complete
local import closure into a fresh artifact directory, under the maintained
shared build lock, using the unchanged pinned Mathlib environment. It verifies
toolchain and dependency revisions, source hashes, and the audit owner set.

The ordinary baseline command

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Modular.AmariChentsovDualConnections
```

exits with code 1 before owner compilation because the configured path package
`external_refs/homotopy-hypothesis-lean4` is missing. Focused validation cannot
certify the root package or replace its pre-push gate.

The fresh focused run passed on 2026-11-20: all five local modules compiled,
and all 99 declarations in the four mathematical owners passed the foundational
axiom audit. The staged proof gate also passed. Exact checked hashes, dependency
revisions, and native results are in
[`observed-results.json`](../verification/statistical-geometry-boundaries/observed-results.json),
with reproduction and coverage notes in the
[verification README](../verification/statistical-geometry-boundaries/README.md).
The root-package limitation remains separate from those successful checks.
