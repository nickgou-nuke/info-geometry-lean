# Real matrix decomposition and metric adjoints

## Provenance and intent

Source: the user's matrix-decomposition message of 2026-11-13, following the
standing request to turn mathematical intake into native Mathlib Lean 4 and
publish a reviewable upstream pull request. The implementation starts at
`a392af178af1fe2bcba2ba39eb405700c6ee103c`. Earlier discussions of twistors,
Clifford algebras, horizons, and information geometry are not hypotheses of
these finite linear-algebra statements.

The source claim is preserved below. The theorem contract then separates
unconditional algebra from invertibility, positivity, and manifold obligations.
Publication is a pull request; no merge is authorized by this task.

## Preserved mathematical intake

For a real square matrix $M\in M_n(\mathbb R)$, the unique decomposition is

$$
M=G+\Omega,\qquad G=\frac{M+M^{\mathsf T}}2,\qquad
\Omega=\frac{M-M^{\mathsf T}}2.
$$

The two parts satisfy $G^{\mathsf T}=G$ and
$\Omega^{\mathsf T}=-\Omega$. Transposing a decomposition gives
$M^{\mathsf T}=G-\Omega$; adding and subtracting recover the two formulas.

Regarding $M$ as a bilinear-form matrix gives
$b(x,y)=x^{\mathsf T}My=g(x,y)+\omega(x,y)$, with
$g(x,y)=x^{\mathsf T}Gy=g(y,x)$ and
$\omega(x,y)=x^{\mathsf T}\Omega y=-\omega(y,x)$.
Symmetry and skew-symmetry are automatic; nondegeneracy requires additional
conditions:

| Interpretation | Additional condition |
| --- | --- |
| Nondegenerate, possibly indefinite metric | $\det G\ne0$ |
| Positive-definite metric | $x^{\mathsf T}Gx>0$ for every $x\ne0$ |
| Symplectic form on the vector space | $\det\Omega\ne0$, forcing even dimension |

An invertible $M$ need not give two nondegenerate parts: $M=I$ has
$\Omega=0$. A symplectic matrix field on a manifold additionally requires
closure, $d\omega=0$.

The two parts generally do not commute. In the full matrix algebra,

$$
M^2=G^2+G\Omega+\Omega G+\Omega^2,\qquad
M^{\mathsf T}M-MM^{\mathsf T}=2(G\Omega-\Omega G).
$$

Thus $G$ and $\Omega$ commute precisely when $M$ is normal for the chosen
Euclidean inner product. The supplied example is

$$
M=\begin{pmatrix}2&3\\1&4\end{pmatrix},\quad
G=\begin{pmatrix}2&2\\2&4\end{pmatrix},\quad
\Omega=\begin{pmatrix}0&1\\-1&0\end{pmatrix},
$$

where $G$ is positive definite, $\Omega$ is symplectic, and

$$
G\Omega-\Omega G=\begin{pmatrix}-4&-2\\-2&4\end{pmatrix}\ne0.
$$

When $G$ is invertible, $A=G^{-1}\Omega$ satisfies
$A^{\mathsf T}G+GA=0$ and $\omega(x,y)=g(x,Ay)$. The identity
$A^2=-I$ is an additional compatibility condition; it does not follow from
the split. Bilinear-form matrices transform by congruence. For a linear
operator, the self-adjoint/skew-adjoint split instead uses the adjoint for a
chosen metric $H$:

$$
M^{\dagger_H}=H^{-1}M^{\mathsf T}H,\qquad
M=\frac{M+M^{\dagger_H}}2+\frac{M-M^{\dagger_H}}2.
$$

This preserved section normalizes the original prose and fixes only Markdown
and mathematical display syntax; it does not replace the claim inventory below.

## Exact carrier and conventions

- Scalars are `ℝ`. Elementary transpose formulas allow any index type `n`.
  Multiplication, determinants, and bilinear forms use `[Fintype n]` and
  `[DecidableEq n]`. Examples use exactly `Fin 2`.
- Matrices act on column vectors. Native `star` on real matrices is transpose.
- The parts are `(selfAdjointPart ℝ M : Matrix n n ℝ)` and
  `(skewAdjointPart ℝ M : Matrix n n ℝ)`. No third definition of the same
  split is introduced.
- `Matrix.toBilin'` is the native coordinate bilinear form.
  `Matrix.PosDef`, `BilinForm.IsSymm`, `BilinForm.IsAlt`,
  `BilinForm.Nondegenerate`, `Matrix.IsAdjointPair`, and
  `Matrix.IsSkewAdjoint` retain their Mathlib meanings.
- The metric-relative adjoint reuses
  `WeightedAdjointCompatibility.adjoint`. A native matrix unit supplies
  invertibility; `Matrix.nonsingInvUnit` connects it to a nonzero determinant.
  Symmetry is a separate hypothesis for involutivity and the eigenspace split.

## Owner search and reuse

The search inspected definitions, imports, proofs, and consumers in `lean/`
and `src/`, and the pinned Mathlib source. The categorical infrastructure map
does not supply a different carrier for this finite matrix task. Optional
graph/oracle services were not used as proof evidence.

| Owner | Reused content |
| --- | --- |
| `Physics/FiniteMetriplecticDynamics.lean` | Existing real `symmetricPart`, `antisymmetricPart`, transpose laws, reconstruction, and both uniqueness lemmas |
| `MassSpectrometry/DirectedOperatorDoubling.lean` | Observed existing `Fin n` split; no duplicate implementation added there |
| `OperatorAlgebra/MatrixOperatorIdentities.lean` | Existing use of native parts for complex matrices; not a real-matrix normality theorem |
| `OperatorAlgebra/WeightedAdjointCompatibility.lean` | Existing unit-weighted adjoint, reverse multiplication, and involutivity for self-adjoint weights |
| Mathlib `Algebra/Star/Module.lean` | Native parts and `StarModule.decomposeProdAdjoint`, a real-linear equivalence giving intrinsic reconstruction and uniqueness |
| Mathlib `Matrix/BilinearForm.lean` | `toBilin'`, symmetry transfer, determinant/nondegeneracy criterion, `toBilin'_comp`, and the bilinear specialization `isAdjointPair_equiv'` |
| Mathlib `Matrix/PosDef.lean` | Native positivity criterion `posDef_iff_dotProduct_mulVec` |
| Mathlib `Matrix/SesquilinearForm.lean` | Relative adjoint predicates and `isAdjointPair_equiv` for metric congruence and operator similarity |

Mathlib's `isStarNormal_iff_commute_realPart_imaginaryPart` assumes a complex
star algebra. It does not give the requested real carrier directly. The new
real identity preserves both ordered products. The two existing owners have
only their broad imports narrowed (and the missing standard header added to
the Physics owner); their mathematical declarations are unchanged.

## Theorem contract and dependency order

| Stage | Exact statement | Hypotheses / boundary |
| --- | --- | --- |
| Native split | Half-sum and half-difference formulas; existing reconstruction and uniqueness | No invertibility or commutation assumption |
| Ordered algebra | Square expansion and transpose-normality defect | Full real matrix multiplication |
| Normality | `IsStarNormal M ↔ Commute G Ω` | No diagonal or commuting restriction imposed in advance |
| Bilinear transport | Native form decomposition, symmetry, and alternation | Finite coordinate space |
| Nondegeneracy | Native determinant criterion; nondegenerate skew form implies even cardinality | Nonzero determinant is explicit; dimension zero is allowed and even |
| Congruence | Parts of $P^{\mathsf T}MP$ equal $P^{\mathsf T}$ times the corresponding part times $P$ | Algebraic identity also holds for singular $P$ |
| Raised index | `G.IsSkewAdjoint (G⁻¹ * Ω)` and the bilinear evaluation identity | $G^{\mathsf T}=G$, $\det G\ne0$, $\Omega^{\mathsf T}=-\Omega$ for skew-adjointness; evaluation only needs invertibility |
| Weighted adjoint | Coordinate formula, native adjoint-pair characterization, linearity, involution, and unique metric split | Unit weight; symmetry additionally for involution and the two eigenconditions |
| Concrete example | Positive $G$, nondegenerate $\Omega$, exact nonzero commutator, $A^2=-\frac14I\ne-I$ | Exactly the supplied `Fin 2` matrices |
| Degeneracy examples | Invertible identity with zero skew part; invertible skew matrix with zero symmetric part | Explicit positive dimension `Fin 2` |

The dependency order is native splitting → bilinear transport and ordered
normality identity; determinant invertibility → raised-index identities;
invertible weight plus symmetry → involutive weighted adjoint → metric split.
The concrete matrix calculations independently witness the limitations.

## Clarifications and scope boundaries

1. For the last formula in the intake, “metric $H$” is made explicit as
   symmetric and invertible. Positive definiteness is unnecessary; indefinite
   symmetric forms are included. A total matrix inverse without the unit or
   determinant hypothesis does not supply these properties.
2. The identity example refutes automatic nondegeneracy of the skew part.
   A separate invertible skew example refutes automatic nondegeneracy of the
   symmetric part. The zero-dimensional exception is avoided by using `Fin 2`.
3. Positivity is proved for `sampleMetric`, not for the nonsymmetric original
   matrix under Mathlib's `Matrix.PosDef` predicate.
4. The supplied example yields
   $A=\begin{pmatrix}1/2&1\\-1/2&-1/2\end{pmatrix}$ and
   $A^2=-\frac14I$. Hence positive $G$ and nondegenerate $\Omega$ do not
   imply that this unnormalized $A$ is a complex structure.
5. Congruence and similarity remain different transformations. The native
   bilinear-form and relative-adjoint change-of-basis results are reused,
   not identified with each other.
6. No smooth manifold, differential-form bundle, exterior derivative,
   closedness theorem, integrable complex structure, or physical consequence
   is constructed. The requirement $d\omega=0$ remains an explicit boundary
   of the finite result, not an unproved premise hidden in a structure.

## Verification contract

The focused package is `verification/real-matrix-split`. It reads canonical
sources in `lean/`, with the root Lean toolchain and exact Mathlib/dependency
pins. `check.py` uses the shared build lock and rejects linked worktrees or
symlinked Lake roots. The aggregate and declaration audit are separate targets.

`audit.py` inventories every explicitly named public declaration in the seven
mathematical owners, including both existing owners whose imports are narrowed.
The generated `RealMatrixSplitAudit.lean` prints transitive axiom dependencies.
The checker rejects missing, duplicate, or unexpected records and any axiom
other than `propext`, `Classical.choice`, and `Quot.sound`. It does not claim to
enumerate every compiler-generated declaration or certify the whole repository.

Final acceptance requires the focused Lake build, fresh audit elaboration,
source/placeholder checks, independent semantic review, and a distinct QA
rerun on the final source hashes. Results and any warnings belong in the
package's acceptance record; this contract alone is not validation evidence.
