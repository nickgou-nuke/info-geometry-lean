# Real operator and divergence contract

## Status and provenance

This change formalizes separate, exact algebraic implications on native Lean/mathlib
carriers: real matrix congruence, symmetric positive-definite matrices, algebraic
primal/dual graphs, and operator blocks over an arbitrary ring. The branches share
some existing definitions; they do not form a theorem deriving one geometric theory
from another.

The mathematical source was checked locally on **2026-11-19**. After the workspace
reset, all **eight Lean files** were recovered on **2026-11-20** and independently
verified to have exactly the previously recorded SHA-256 hashes. This verifies the
recovered source bytes; it is not a new compilation result.

The original unpublished local commit `8856fdc4` and its transient build artifacts
were lost. Recovery uses the original GitHub base
`fea96b564201654cd4693008585039a56f66adf3` and the recorded final source. Any recovered
publication has a **new commit SHA**, recorded on the draft pull request; the
historical commit identifier does not identify that recovered commit. Acceptance
metadata, the verification runner, and CI configuration are reconstructed artifacts,
not recovered historical execution logs.

See [the acceptance record](../verification/real-operator-divergence/ACCEPTANCE.json)
and [the verification runner](../verification/real-operator-divergence/audit.py)
for the source inventory, provenance, and commands for a current validation run.
At recovery, no fresh local compilation or current remote CI result had been
established. A later run must be identified by its own commit and result.

## Canonical ownership and imports

Paths below are relative to `lean/InfoGeometry/`. Consumers should import the owner
of the result they need. This table lists the proof inputs relevant to this change;
it is not an exhaustive transitive import or kernel-dependency export.

| Canonical owner | Native carrier and principal reused inputs |
| --- | --- |
| `Architecture/MatrixSymmetricConeFisherRao.lean` | Arbitrary finite real matrices. Imports `InfoGeometry.OperatorAlgebra.RealMatrixSplit` and Mathlib matrix trace/inverse APIs; reuses the owner's existing Fisher symmetry, congruence invariance, identity evaluation, and symmetric sum-of-squares results. |
| `Jordan/SPD.lean` | Existing `SPD n` with an actual real matrix and symmetry/positive-definiteness proofs. Mathlib `Matrix.PosDef`, `Matrix.isSymm_one`, `Matrix.PosDef.one`, and positive scalar multiplication construct the new values. |
| `Jordan/BurgStein.lean` | Imports `InfoGeometry.Jordan.LogDet`, hence the existing SPD determinant and normalized-distortion APIs. Uses native matrix inverse, trace, determinant, continuous functional calculus square root, and real logarithm identities. |
| `Geometry/DualFlatKreinLegendreGraph.lean` | `V × Module.Dual ℝ V` for an arbitrary real module. Imports `InfoGeometry.Clifford.NeutralPhaseSpaceCore`, `Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal`, and `Mathlib.LinearAlgebra.Prod`. |
| `OperatorAlgebra/RealMatrixSplit.lean` | Arbitrary finite real matrices, using the native self-adjoint/skew-adjoint split, transpose, and trace APIs. |
| `OperatorAlgebra/PeirceSpine/CyclotomicGaloisNilpotentSylvesterSynthesis.lean` | Existing `sylvesterBlockMat` over `[Ring B]`. Reuses the owner's block extensionality and unipotent diagonalization/power theorem, native polynomial evaluation, and centrality of integer casts. |
| `Algebra/CyclotomicRealCounterexamples.lean` | Concrete real matrices and nested real block matrices. Imports `InfoGeometry.Algebra.LieCyclotomicBridge`, the Sylvester owner above, and `InfoGeometry.Algebra.Quantum.QBinomial`. |

The eighth recovered file, `OperatorAlgebra/RealMatrixSplitAudit.lean`, is an audit
companion. It lists declarations for axiom inspection and is not a mathematical
umbrella import. Its legacy audit scope is separate from the seven-owner audit of
this change.

## Exact mathematical scope

### Congruence pullback of the Fisher form

The owner defines the real-valued bilinear expression

$$
 g_P(U,V)=\frac12\operatorname{tr}(PUPV)
$$

and the full congruence tangent

$$
 T_\Sigma(A)=A\Sigma+\Sigma A^T.
$$

`congruenceAction_affine_generator` proves the exact polynomial expansion of
`(I+tA) Σ (I+tA)ᵀ`. If `A=S+Ω`, with `Sᵀ=S` and `Ωᵀ=-Ω`, then

$$
 T_\Sigma(A)=(S\Sigma+\Sigma S)+(\Omega\Sigma-\Sigma\Omega).
$$

`fisherRaoMetric_congruenceTangent_split` retains the mixed term between these two
summands. The skew contribution need not vanish at an anisotropic covariance.
At the identity covariance the tangent is twice the native self-adjoint part.

For a real Gram frame with **both** `H*G=1` and `G*H=1`, the proved pullback is

$$
 g_{H^T H}\bigl(T_{GG^T}(A),T_{GG^T}(A)\bigr)
 =2\sum_{i,j}\bigl(\operatorname{sym}(HAG)_{ij}\bigr)^2.
$$

Here `sym` denotes the native `selfAdjointPart ℝ`. The value is nonnegative,
and it vanishes exactly when `(H*A*G)ᵀ=-(H*A*G)`.
No diagonalization or matrix-commutation hypothesis is introduced.

The existing `fisherRaoMetric_congruence_invariant` API now requires only the
left-inverse identity actually used by its proof. The Gram tangent identity uses
the other direction, so the Gram pullback still retains both inverse hypotheses.
The sole repository caller of the changed API was updated after a caller search
covering `lean`, `src`, `tests`, and `proofs`.

### Full SPD scaling and the unique positive-ray optimum

`SPD.identity n` constructs the identity covariance, with its matrix readout and
an `Inhabited (SPD n)` instance. `SPD.rescale` constructs an SPD matrix from a
strictly positive real scalar and an existing SPD matrix.

For `X,Y : SPD n`, write

$$
 D(X,Y)=\operatorname{tr}(Y^{-1}X)-\log\det(Y^{-1}X)-n,
 \qquad b(u)=u-\log u-1.
$$

For positive `r,s`, `steinLoss_rescale` proves

$$
 D(rX,sY)=\frac r s\operatorname{tr}(Y^{-1}X)
 -n\log(r/s)-\log\det(Y^{-1}X)-n.
$$

Common positive scaling therefore preserves the loss. For determinant-one
`X,Y`, the exact scale/shape formula is

$$
 D(rX,sY)=n\,b(r/s)+(r/s)\bigl(\operatorname{tr}(Y^{-1}X)-n\bigr).
$$

When `0<n`, `normalizedDistortion_trace_pos` proves
`t=tr(Y⁻¹X)>0` using a positive square root of `Y⁻¹`, positive-definite congruence,
and cyclic trace. It does not assume that `Y⁻¹X` is symmetric. With
`r*=n/t`, the exact gap is

$$
 D(rX,Y)-D(r^*X,Y)=n\,b(r/r^*) \qquad (r>0).
$$

The scalar Burg inequality gives the global minimum **on this positive ray**;
equality holds exactly at `r=r*`. Strict trace/scale positivity and uniqueness
retain `0<n`. The determinant-one assumptions occur only in the shape formula.

### Algebraic graph orthogonality and the trace obstruction

For `L : V →ₗ[ℝ] Module.Dual ℝ V`, the native neutral skew form satisfies

$$
 (\operatorname{graph}L)^{\perp_\omega}=\operatorname{graph}(L.\mathrm{flip}).
$$

The orthogonal convention is `ω Y X=0` for every `Y` in the submodule. A graph
is self-orthogonal exactly when its duality pairing is symmetric. For such a
symmetric `L`, every isotropic submodule containing its graph equals that graph.
These statements use the
algebraic dual and require no finite-dimensionality, convexity, or smoothness.

The real matrix trace results prove

$$
 \operatorname{tr}(G\Omega)=0
 \quad(G^T=G,\ \Omega^T=-\Omega),
$$

and consequently

$$
 \operatorname{tr}\bigl(\rho(AB-BA)\bigr)=0
 \quad(\rho^T=\rho,\ A^T=A,\ B^T=B).
$$

The symmetric weight need not be positive or normalized. The commutator is formed
in the matrix algebra before taking the trace; its vanishing is not asserted.

### Noncommutative Sylvester blocks and exact counterexamples

For the native upper-triangular block `M(A,C,Y)`, with diagonal blocks `A,C`
and upper-right block `Y`, multiplication and powers retain their ordered
products over any `[Ring B]`:

$$
 M(A,C,Y)^n=M\left(A^n,C^n,
   \sum_{k=0}^{n-1}A^kYC^{n-1-k}\right).
$$

The sum is empty when `n=0`, and `Y` is arbitrary. For the specifically
constructed block `Y=XC-AX`, every
**integer polynomial** satisfies

$$
 p(M(A,C,XC-AX))
 =M\bigl(p(A),p(C),Xp(C)-p(A)X\bigr).
$$

This yields the exact polynomial-root equivalence with the two diagonal
operators. It neither assumes commuting diagonal operators nor solves an
arbitrary Sylvester equation.

The finite real counterexamples separately prove that:

- A real cubic companion can satisfy `I+R+R²=0` while `tr R=-1`.
- Two conjugate real block matrices can fail to commute while each matrix and
  their product satisfy the cubic cyclotomic polynomial.
- At the nonprimitive fourth root `q=-1`, the geometric sum vanishes but the
  native coefficient `qBinomial q 4 2` equals `2`.

These exact examples restrict overstrong general implications. They make no
claim that these behaviors hold for every operator or every root of unity.

## Proved dependency order

The following records the actual proof branches, rather than a proposed causal
interpretation of the intake. Definitions and existing results remain distinct
from new theorem implications.

| Branch | Proof order and boundaries |
| --- | --- |
| Fisher polarization | Existing Fisher symmetry gives `fisherRaoMetric_add_self`; together with `congruenceTangent_of_split`, this gives the mixed-term pullback. |
| Fisher Gram transport | `congruenceTangent_gram` and existing congruence invariance give `fisherRaoMetric_congruenceTangent_gram`. Existing identity evaluation, symmetric trace squares, and the native half-sum formula then give the sum-of-squares result and nonnegativity. |
| Fisher nullspace | Gram transport and the existing identity nullspace theorem give the exact skew-generator criterion directly. This proof does not invoke the new nonnegativity theorem. |
| SPD scaling | Positive scalar multiplication constructs `SPD.rescale`; native inverse scaling gives `normalizedDistortion_rescale`; trace/determinant/logarithm identities give the two-scale loss. Common scaling and determinant-one shapes are consequences. The one-sided loss proof evaluates its distortion directly. |
| Burg optimum | Native square-root congruence gives positive distortion trace, hence positive `steinRayScale`. Both actual losses are expanded before the private real arithmetic lemma `real_log_ray_gap` is instantiated with the native dimension, trace, and log determinant. The resulting gap gives the minimum; the scalar kernel's exact zero criterion gives uniqueness separately. |
| Graph | Native graph membership and orthogonal membership give the flipped-graph identity; that identity gives symmetry/self-orthogonality; antitonicity of orthogonal submodules gives maximality. |
| Trace | Transpose and cyclic trace give symmetric/skew trace vanishing; applying it to the skew commutator of two symmetric matrices gives the weighted result. |
| Sylvester | Block multiplication and induction give the arbitrary-insertion power formula. Polynomial transport instead reuses the owner's pre-existing specialized power formula and integer-cast centrality; the root equivalence follows from that transport. |
| Counterexamples | The cubic examples are evaluated entrywise using the existing real companion and native cubic cyclotomic polynomial. Their conjugating inverse reuses the existing Sylvester inverse theorem. The quantum-binomial example evaluates its native coefficient independently. |

In particular, the Fisher proofs do not derive their metric from Burg divergence;
the graph proofs do not depend on Fisher positivity; and the finite cubic examples
do not invoke the new general integer-polynomial theorem. The Fisher owner reuses
the pre-existing self-adjoint-part formula, not the newly added trace-obstruction
lemmas.

## Validation history and recovery boundary

### Recorded local results — 2026-11-19

| Check | Historical result and scope |
| --- | --- |
| Native seven-owner audit | Passed for **466 declarations across seven mathematical owners**. This counts the audited owner declarations, not 466 newly added theorems. The reported axiom union was exactly `propext`, `Classical.choice`, and `Quot.sound`. |
| Legacy real-matrix audit | Passed for **83 explicitly named declarations** in its separate maintained audit scope. This is not an additional count of new theorems. |
| Strict OpenGauss source screen | Passed with **0 traps** on the checked change scope. A source screen is separate evidence from kernel compilation and semantic review. |
| Root pre-push path | Failed **before elaboration** because `external_refs/homotopy-hypothesis-lean4` was missing. This is an unresolved root-environment exception, not a successful repository-wide build. |

These results were recorded before the workspace reset. Exact source recovery
preserves the checked mathematical bytes, but does not recreate the lost build
cache, original execution logs, or original commit object. The historical axiom
report does not claim constructive logic without classical choice or an axiom
certificate for the whole repository. Historical owner builds retained existing
warnings; this record does not assert warning-free compilation.

### Recovery and publication — 2026-11-20

All eight Lean source hashes were independently checked against the recorded
final values. Documentation, acceptance metadata, and CI/runner files have been
reconstructed to explain provenance and permit a fresh check. Their reconstruction
must not be reported as a successful new Lean run.

The user explicitly authorized a **draft pull request** with the known root
pre-push exception. That authorization permits publication for review; it does
not resolve the missing external dependency or establish a globally green build.
Use the acceptance record and the actual current CI run for subsequent validation
status, keeping historical local results and new execution results separate.

## Nonclaims

This change does not prove a Gaussian-measure formula for KL divergence, a KL
Taylor theorem, or a global smooth Fisher metric construction. The Fisher
pullback here is an exact algebraic evaluation. The Burg result proves a positive-ray
optimum and its gap; it does not establish nonnegativity of the full matrix loss
for every pair by a new theorem, nor replace the distortion by commuting matrices.

Graph self-orthogonality does not supply a convex potential, a smooth Legendre
transform, a dually flat statistical connection, or positivity of the neutral
form. The real weighted-trace identity does not identify a quantum curvature or
KMS structure. Cyclotomic equations and finite counterexamples do not construct a
Kähler structure, gauge theory, or general noncommutative exponential family.

No universal real matrix logarithm, unconditional orthogonality of covariance
scale/shape/skew contributions, arbitrary-coefficient noncommutative polynomial
calculus, or positive super-probability/Berezinian divergence is claimed. Those
claims require additional hypotheses or separate constructions beyond these
native proofs.
