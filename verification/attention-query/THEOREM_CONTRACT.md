# Attention query geometry and prescribed spiral flow

## Provenance and intended scope

Intake: the user's 2026-11-25 conversation proposing a Transformer attention /
plabic Dirac / Souriau Massieu correspondence and a loxodromic explanation of
"spiralism". Implementation baseline: `fe24e350b08fdea04f74c0748ef9fd9417c47529`
in `nickgou-nuke/info-geometry-lean`. The exact filename
`LoxodromicTwinThermalWaves.lean` was not found in the inspected repository trees
or by the connected GitHub default-branch code search. Related owners below are
the source authority. No claim about all remote branches is made.

The primary mathematical carrier is a real normed space `E`, a nonempty finite
family of continuous key covectors `K : Fin M → E →L[ℝ] ℝ`, and a real inverse
temperature `β`. Define `s(q)_j = β K_j(q)`,
`Φ(q) = log(Σ_j exp(s(q)_j))`, and `p_j(q) = exp(s(q)_j)/Σ_l exp(s(q)_l)`.
All new mathematical constructions use real scalars; no complex scalar or
imaginary unit is introduced by this addition.

## Intake claim ledger

| Supplied claim or theme | Exact treatment |
|---|---|
| Recursive Socratic dialogue necessarily converges to a spiral | Empirical/cognitive interpretation; no data or dynamical model supplied. No theorem asserted. |
| Straight line / circle / spiral as progress and recurrence | Metaphor retained as intake, without a mathematical implication about dialogue. |
| Rotation plus translation equals a helix / spiral | Requires a specified screw motion; planar logarithmic spiral here uses uniform scaling plus rotation. |
| Loxodromic null scaling and transverse rotation produce a spiral | Prove the explicit projective chart identity after dividing by a nonzero boosted null coordinate. |
| Exponential scaling is inherently irreversible or entropy-producing | Rejected as a general implication: the prescribed finite-time matrix has an exact inverse. |
| Any metriplectic/GENERIC rotation with drift inevitably spirals | Overstrong. An anisotropically damped real matrix with nonzero rotation has an explicit straight invariant ray. No universal GENERIC theorem is claimed. |
| Training-data archetypes, DNA/Fibonacci/Jung/Hegel motifs explain model output | Narrative hypotheses, not proved by the algebra or supported here by experiments. |
| Attention/residual depth yields a loxodromic 4-screw | No supplied layer recurrence identifies this dynamics. Prove only the actual ODE of the existing prescribed spiral. |
| Query/key pairing is neutral bipartite evaluation | Reuse canonical primal/dual null inclusions and prove the matrix-logit evaluation bridge. |
| Queries cannot pair with queries algebraically | The chosen null embeddings have zero neutral pairing; ordinary vectors can still have nonzero Euclidean self-pairings. |
| Ordinary query/key sectors equal graphs of an arbitrary skew Poisson map | Additional map and hypotheses required; canonical primal/dual summands and opposite skew graphs are distinct constructions. |
| Attention logits have rank d and are Plücker coordinates | Prove rank at most d. Maximal minors of suitable full-rank representatives, not arbitrary logit entries, provide Plücker coordinates. No planar embedding or positivity is constructed. |
| Low-rank logits imply low-rank attention probabilities | Refuted by symmetric rank-at-most-one logits whose row softmax has rank two. |
| Softmax is Gibbs and log-sum-exp is a Massieu potential | Existing normalized finite exponential-family calculus is reused. β remains explicit. |
| Softmax is the "Legendre–Fenchel gradient" | Correct formulation is gradient of log-partition. Full extended-real conjugacy on the closed simplex is not asserted. Existing interior Gibbs variational owners are identified separately. |
| Fisher equals log-partition Hessian / covariance | Prove the query-space Fréchet derivative, actual log-probability score derivative, second line derivative, and Fisher equality. |
| This automatically yields a Riemannian semantic metric or dissipation | The form is only semidefinite without separation of query directions by key differences. Semantic interpretation and dissipative evolution are not implied. |
| Q/K exchange and transpose are the Dirac CPT mirror | Prove Q/K exchange transposes logits. The real sign mirror preserves pure coordinate sectors and is not a role exchange. No physical CPT is constructed. |
| Transpose reverses normalized attention | Prove transpose exchanges row and column normalization, and give an exact counterexample to commuting row softmax with transpose. Mask reversal and stochastic time reversal are separate operations. |
| RoPE realizes relative rotations | Existing real rotation owners already prove this. New flow results build on the existing real rotor. |
| SCFG, Markov chains, GloVe/Word2Vec/PMI are the same construction | These require distinct probabilistic assumptions/objectives; no new grammar or embedding-factorization theorem is claimed. |
| A Casimir center stores invariant semantics | No Poisson algebra, Casimir map, semantic observable, or invariance proof is supplied. Retained as open interpretation. |
| All relational graph models are forced into one spin-network universality class | No classification theorem follows from bilinearity. Spin-network representation/intertwiner data and plabic planarity remain extra structure. |
| Physical and linguistic units differ | Scope distinction retained: finite statistical/matrix results do not identify token space with physical spacetime. |

## Reused owners and actual dependencies

- `Canonical.AttentionInformationGeometry`: real logit softmax, coordinate and
  line derivatives, covariance, positivity iff a logit direction is nonconstant.
  Its analytic roots are `Analytic.LogSumExp` and
  `Analytic.LogSumExpVariancePositivity`. These contain actual calculus, not
  structures assuming desired derivatives.
- `Canonical.NeutralDualPairSplitting` and `Clifford.NeutralPhaseSpaceCore`:
  existing primal/dual inclusions, evaluation form, null sectors, and para map.
- Native Mathlib matrix multiplication, transpose, rank, determinant, dual
  `dotProductEquiv`, continuous linear maps, Fréchet and ordinary derivatives.
- `Rotary.RotarySpiralBridge`: existing real rotor and
  `loxodromicSpiralMatrix λ ω t = exp(-λt) • ropeRotor ω t`.
- Existing broader `QuantumContext.RotaryAttentionSpiralDynamics` and
  `Canonical.AttentionRelativeGroupBridge` explain related source coverage;
  they need not be imported into the small new flow owner.
- `Thermodynamics.SoftmaxGibbsVariationalPrinciple` and
  `SoftmaxGibbsVariationalClosure` already establish an interior-simplex
  variational principle. They are not a closed-simplex Fenchel conjugacy result.

## Acceptance statements

1. The genuine Fréchet derivative is `β • Σ_j p_j(q) • K_j`.
2. The actual derivative of `log p_j(q+t u)` is
   `β (K_j(u) - Σ_l p_l(q) K_l(u))` at zero.
3. The second line derivative and the expected squared actual score both equal
   `β² Σ_j p_j(q) (K_j(u)-Σ_l p_l(q)K_l(u))²`.
4. This is nonnegative for every β. For β ≠ 0 it is zero exactly when all
   keys agree on u, and positive exactly when two keys distinguish u.
5. `Q*Kᵀ` is the actual neutral evaluation matrix, transposes under exchanging
   the input families, and has rank at most the latent dimension.
6. A symmetric factorized 2×2 score matrix has nonsymmetric row softmax with
   determinant `(exp 1 - 1)/(2*(1 + exp 1)) > 0` and rank two.
7. The existing prescribed real spiral satisfies the genuine vector ODE
   `x' = κ x + ω J x`, real-time composition, and exact inverse laws.
8. With nonzero null coordinate u, division by its boost produces exactly the
   prescribed planar scale-rotation in the projective chart.

## Dependency order

Key evaluation → logits → log-partition and probabilities → actual derivatives
→ Fisher covariance → nonnegative/null-direction statements.

Neutral inclusions → matrix evaluation → transpose/rank; exponential
normalization → explicit counterexample. These do not imply physical CPT.

Existing real rotor and exponential scale → matrix addition law → negative-time
inverse law. Differentiating the prescribed exponential/trigonometric
coefficients independently gives the ODE. Exponential inversion and scalar
division independently give the projective-chart identity. No edge connects
an unspecified Transformer residual update to this prescribed differential
equation.

## Validation contract

Preserve Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Use the repository shared build lock.
Compile new owners and their actual repository import closure; inspect all
new declaration axiom dependencies, accepting only `propext`,
`Classical.choice`, and `Quot.sound`. New owners must contain no proof holes,
custom axioms, unsafe shortcuts, or `native_decide`. Keep root-workspace Lake
coverage distinct from an isolated exact-pin source-closure check. Record any
pre-existing source/dependency failure without weakening the requested proofs.

Independent semantic review and a separate verification review are required.
The user requested publication as a pull request on 2026-11-25. Publish this
source-reviewed implementation as a draft while compilation and declaration
axiom checks remain pending. Publication does not assert verification or
authorize a merge; the acceptance conditions above remain outstanding.
