# Weyl scaling, relative Dikin geometry, and positive coarse-graining

## Provenance and exact scope

This task formalizes the user's proposal that Weyl scaling and Dikin ellipsoids
provide reusable estimates for the Wilson renormalization-group project. The
implementation target is `nickgou-nuke/info-geometry-lean`; the potential consumer
is [MathePhysics/4D_Wilson_Loop_RG](https://github.com/MathePhysics/4D_Wilson_Loop_RG),
inspected at `9a4492cc6bdf3338379123a085af59dfd8018a9c`.

The contracts below concern finite, full, generally noncommuting precision
matrices and an operator-norm inverse estimate. A Wilson renormalization step,
a running coupling, or a continuum limit is not a definition in this change.

## Existing owners

- `Analysis/PositiveMatrixDikin.lean` owns `inverseSqrt`,
  `normalizedVariation`, `traceQuadratic`, their trace identities, and Dikin
  positivity/order estimates on full complex matrices.
- `OperatorAlgebra/PositiveCoarseGraining.lean` owns the rectangular Schur
  precision and harmonic extension, with positivity derived from positive input
  matrices.
- `OperatorAlgebra/CoarseGrainingVariational.lean` proves the exact minimum of
  the Hermitian quadratic energy and uniqueness of its fine minimizer.
- Native Mathlib owns matrix nonsingular inverse, cyclic trace, matrix
  positivity, continuous functional calculus, and the convergent geometric
  inverse series.

These definitions and proofs are reused. No diagonalization, commuting
assumption, supplied minimizer, or supplied inverse is introduced as a
replacement for the full operator problem.

## Mathematical contracts

### 1. Change of frame and Weyl scaling

For finite square matrices over a commutative star ring, an invertible matrix
`C` acts on both the precision and its variation by congruence:

\[
 P' = CPC^*,\qquad H'=CHC^*.
\]

The ordered mixed inverse trace is invariant. In particular, the existing
complex Dikin quadratic satisfies

\[
 q_{P'}(H')=q_P(H),\qquad
 q_P(H)=\operatorname{ReTr}((P^{-1}H)^2).
\]

The algebraic congruence equality needs only invertibility of `C`. Strict
positivity of `P` and self-adjointness of `H` enter when applying the existing
Dikin nonnegativity and containment theorems. Simultaneous positive scalar
scaling gives `q_(cP)(cH)=q_P(H)`.

### 2. Relative stability under exact elimination

Let `A : Matrix n n 𝕜` and `R : Matrix m m 𝕜` be positive definite over an
`RCLike` field, and fix a rectangular `Q : Matrix m n 𝕜`. Reuse

\[
 H=A+Q^*RQ,\quad E=H^{-1}Q^*R,\quad
 S=R-RQH^{-1}Q^*R.
\]

The variational theorem gives joint Loewner monotonicity, simultaneous
homogeneity `S(cA,cR,Q)=cS(A,R,Q)` for `c>0`, and scale invariance of `E`.
For `0 ≤ r < 1`, positive definite `A'`, `R'`, and the input sandwiches

\[
 (1-r)A\preceq A'\preceq(1+r)A,\qquad
 (1-r)R\preceq R'\preceq(1+r)R,
\]

the output satisfies the same relative bounds:

\[
 (1-r)S(A,R,Q)\preceq S(A',R',Q)\preceq(1+r)S(A,R,Q).
\]

Native `Matrix.PosSemidef` differences express the order, avoiding entrywise
order ambiguity. The proof evaluates the two energies at their already proved
minimizers. It covers arbitrary finite dimensions and full noncommuting
matrices. The observation map `Q` is held fixed.

### 3. Relative perturbation and the inverse bound

For a positive invertible operator `P`, normalize a perturbation `E` by

\[
 B=P^{-1/2}EP^{-1/2}.
\]

The smallest missing analytic implication is to combine the native geometric
inverse series with the ordered factorization

\[
 P+E=P^{1/2}(1+B)P^{1/2}
\]

and prove invertibility and a bound on its normalized inverse. The target is
`‖B‖ ≤ r < 1` implying a bound `1/(1-r)`, and hence the factor-two estimate at
`r=1/2`. The implementation must state its complete normed-ring/C-star
assumptions explicitly and construct the inverse from smallness.

### 4. Composed Dikin consumers

For self-adjoint perturbations `DA`, `DR`, bounds
`sqrt(traceQuadratic A DA) ≤ r` and `sqrt(traceQuadratic R DR) ≤ r`, with
`0 ≤ r < 1`, supply positivity of `A+DA`, `R+DR` and the coarse relative
sandwich in contract 2. Positivity of the perturbed inputs is derived.

Similarly, the Dikin trace radius bounds the normalized operator norm in
contract 3 and yields the normalized inverse estimate. This is the concrete
dependency from the existing Dikin owner to the new Schur and inverse results.
It does not assert that Schur elimination contracts the trace Dikin radius.

## Consumer map and remaining work

| External owner | Relevant contract | Still required for a direct application |
| --- | --- | --- |
| `CoreLean/LandauNeumann.lean` | `series_right_inverse`, `series_left_inverse`, `series_bound` | Identify the actual propagator/perturbation and prove the norm comparison to its `‖G * Δ'‖ ≤ 1/2` hypothesis. |
| `CoreLean/FixedPointBall.lean` | `fixed_point_ball` | Prove that the actual nonlinear map preserves the ball and has the required Lipschitz bound. |
| `GaussianBlockSpin/UnitScaleLaws.lean` | `gaussProb_eq_map_unit` | Match precision and field-scaling conventions; the measure pushforward already exists there. |
| `CoreLean/CubicNorms.lean` | Weighted supremum/gradient norms | Establish scale-uniform comparison constants; finite-dimensional norm equivalence alone does not supply them. |

The local pin is Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The external packages use different
pins. Compilation here is not a compilation result for their project.

In normalized coordinates the external Neumann interface can use `Δ=1`,
`Δ'=-B`, `G=1`. The new ordered inverse identity supplies the transport back
to the original coordinates. This does not replace the original norm
comparison. For example, `P=diag(ε²,1)` and
`E=rε * !![0,1;1,0]`, with `0<ε<1`, give normalized perturbation norm `r`
but original Euclidean norm `‖P⁻¹E‖=r/ε`. Uniform conditioning or an explicit
energy-norm realization is necessary for that additional claim.

## Acceptance targets

Compile the complete repository import closure from copied and hashed source,
then audit all declarations owned by the selected modules against the allowed
foundational axioms. Also run the staged proof gate, scope/semantic checks, and
the applicable post-build gate, reporting each result at its actual scope.
No proof holes, custom axioms, or unsafe proof shortcuts are accepted.

## Implemented and locally checked results

The five new owners compiled together with their complete ten-module repository
import closure at local commit `ed85b573863e0ee5197708216f74bc552ee4ca27`, using
Lean `v4.34.1` and the unchanged Mathlib pin. Every module reported zero warnings.
All repository modules were rebuilt from copied, hashed source; existing
repository oleans were not reused. The existing pinned Mathlib and dependency
artifacts were read without copying their caches into the full workspace.

| Selected owner | Native declarations audited |
| --- | ---: |
| `Analysis.PositiveMatrixDikinCongruence` | 9 |
| `Analysis.RelativeOperatorNeumann` | 12 |
| `OperatorAlgebra.CoarseGrainingRelativeStability` | 11 |
| `Canonical.RelativeDikinCoarseGraining` | 4 |
| `Canonical.WeylDikinRGTests` | 32 |
| **Total** | **68** |

The audit enumerated every declaration owned by those modules, including private
and generated declarations, rejected unsafe/partial declarations, and collected
axiom dependencies natively. The only dependencies were `propext`,
`Classical.choice`, and `Quot.sound`. The
[validation record](verification/weyl_dikin_rg_20261124.json) includes the exact
source hashes and dependency revisions. The count is a declaration count, not a
claim of 68 independent mathematical theorems.

The example computes the actual inverse quadratic of
`P = !![2,1;1,2]` and `H = (1/4) • !![1,1;1,-1]` as `1/9`, proves
`P*H ≠ H*P`, and uses the invertible nonunitary shear `!![1,1;0,1]`.
It consumes both the normalized inverse estimate and the rectangular coarse
sandwich with `Q = !![1,1]`, observation precision `1`, and zero observation
perturbation.

## Reproduction and integration status

The maintained scoped verifier uses the same source-closure and native
declaration-audit helpers as the existing operator-geometry checks:

```bash
python3 tools/quality/check_weyl_dikin_rg.py \
  --mathlib-root /path/to/pinned-mathlib \
  --output /new/path/to/weyl-dikin-verification --fetch-cache
```

The Mathlib checkout and active compiler must match the pins; the verifier
rejects mismatches. The output directory must be new. The dedicated
`weyl-dikin-rg.yml` workflow provisions those exact dependencies and runs this
command in GitHub Actions.

The actual pre-commit proof gates passed during the implementation. Selected
source debt, semantic-content, authoritative-source, and semantic-vacuity
checks passed. The ordinary root pre-push gate was also attempted: its Lake
step failed while cloning Mathlib with `No space left on device`; its selected
source checks passed. That result is an infrastructure failure, not a successful
root-package build. No root gate or dependency pin was changed.

The local result certifies the stated source closure and selected declarations.
Hosted CI remains a separate check, and an upstream build against the Wilson
project's different pins remains separate work. The PR stays a draft while
those integration checks are outstanding.
