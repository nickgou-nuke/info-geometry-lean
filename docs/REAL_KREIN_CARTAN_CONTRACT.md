# Real Krein–Cartan operator identities: theorem contract

## Intake and scope

This change formalizes the real operator content of
`Pasted text(20261117-084740).txt`, supplied on 2026-11-17. The frozen input has
SHA-256 `8ea38c11ad3a8d7510ce47cec9100d9a61c81e6b76ee7ef004e5784622fda03a`.
The original attachment remains the provenance record. Its narrative,
psychological descriptions, proposed causal diagram, and assertions of
verification are not proof premises.

The starting repository revision is
`08c34e03f610b452e03422037949196dc7d92d6d`. The dependency contract is unchanged:
Lean `v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
All matrix statements use native `Matrix n n ℝ`, with finite `n`; operator
products remain ordered. General weighted-adjoint statements use the existing
owner on an arbitrary associative star ring. No external complex scalar is
introduced into these carriers.

## Source-grounded reuse

| Existing owner | Actual interface and hypotheses | Role in this change |
|---|---|---|
| `OperatorAlgebra/WeightedAdjointCompatibility.lean` | `adjoint w x = ↑w⁻¹ * star x * ↑w`, for a unit `w` in a star ring; `adjoint_mul`; `adjoint_involutive` requires a self-adjoint weight; `adjoint_eq_star_iff` characterizes commutation. | Extend the same adjoint with equality/relative-center and transport results, rather than define a competing adjoint. |
| `OperatorAlgebra/RealMetricAdjoint.lean` | Real matrix inverse-transpose formula; native `Matrix.IsAdjointPair`; uniqueness for an invertible weight; self/skew-adjoint splitting. | Recover a matrix weight from equality of adjoint maps, using native matrix-center lemmas. |
| `Krein/KreinCartanOperatorDecomposition.lean` | Continuous operators on `InvolutiveSelfDualCarrier`; conjugation by the supplied involution; projection and reconstruction identities. | Existing continuous-carrier decomposition is retained. A finite trace theorem does not assert its extension to arbitrary continuous operators. |
| `Canonical/RealSplitKreinHilbertizationBridge.lean` | Krein adjoint and parity comparison on the specific `Mat32` carrier, with the Cl55 import closure. | Existing specialized result; the new finite trace bridge treats arbitrary finite real matrices without replacing the Cl55 representation. |
| `OperatorAlgebra/PeirceTraceForms.lean` | Ordered Peirce trace forms, including a grading inserted once in a trace. | Distinct from `Tr((η Aᵀ η) B)`; a shared word such as “Krein” does not identify the forms. |
| `Canonical/BogoliubovFrameKreinMetricBridge.lean` | Pullback metric `U.adjoint ∘ G ∘ U` and self-adjointness on a doubled Hilbert carrier. | Reused as a scope comparison; the finite transport statements require actual inverse frames and retain the multiplication order. |
| `CliffordWeyl/DiracMetricCovariance.lean` | Full matrices over a star ring, with mutually inverse frames `S,T` and separate inverse metrics `η,ξ`; transported inverse laws and `metric_adjoint_change_basis`. | Reuse the existing ordered covariance result when connecting inverse congruence to the unit-valued weighted-adjoint interface. |

Searches covered relevant declarations, alternate formulations, imports and
consumers in `lean/InfoGeometry`, with corresponding `src/InfoGeometry` owners
checked where applicable. They were bounded source searches, not a certificate
of absence throughout every historical directory. The tracked declaration-DAG
snapshot (`lean/DAG/decls.jsonl`, 2,625 rows; `decl_edges.jsonl`, 5,211 rows) has no
hit for the selected weighted-adjoint/real-metric owner names. Its initial rows
use `unknown_module`, and source-revision freshness was not established. It is
therefore not used as evidence that a bridge exists or is missing. The actual
Lean imports and proof references determine the dependencies below.

## Exact mathematical targets

### 1. What a weighted adjoint determines

Fix the reference star operation, and write
`J_w(x) = w⁻¹ star(x) w`. The proposed extension proves

\[
J_w(x)=J_z(x)
\quad\Longleftrightarrow\quad
\operatorname{Commute}(\operatorname{star}(x),wz^{-1}).
\]

Consequently `J_w = J_z` exactly when the relative weight `w z⁻¹` commutes
with every element. In a full finite real matrix algebra, native matrix-center
results imply `w = c • z` for a real scalar `c`. If the index type is nonempty,
invertibility forces `c ≠ 0`. If both weights square to the identity, equality
of the adjoints is equivalent to `w = z ∨ w = -z`.

This is a recovery result with a fixed reference transpose. Symmetry is not
needed for the recovery implication itself; it is the sufficient hypothesis
used by the existing involutivity theorem. The zero-dimensional matrix algebra is
handled separately by the exact hypotheses of the statements.

### 2. Real grading and trace forms

Let `ηᵀ = η` and `η * η = 1`, and put `τ(A) = η A η`. The parity projections
are `(A + τ(A))/2` and `(A - τ(A))/2`. Their reconstruction and eigenspace
laws precede the trace results. The existing weighted adjoint is connected to
the concrete expression `η Aᵀ η`, and hence to `(τ(A))ᵀ`.

For arbitrary real matrix weights `L, R`, define the ordered kernels

\[
H_{L,R}(U,V)=\operatorname{Tr}(L U^\top R V),\qquad
B_{\eta;L,R}(U,V)=\operatorname{Tr}(L(\eta U^\top\eta)R V).
\]

The reciprocity identities
`B(U,V) = H(τ(U),V)` and `H(U,V) = B(τ(U),V)` do not require `L` or `R`
to commute with `η`. Invariance under simultaneous parity, and orthogonality
of opposite parity sectors, do require that commutation. No commutation of
`U` and `V`, or of `U` with either weight, is assumed.

For identity weights, the native Gram trace is nonnegative and is zero
exactly for the zero matrix. This gives strict positivity for nonzero
matrices, strict negativity of the Krein trace on nonzero odd matrices, and
the signed quadratic decomposition into the two parity components. These
are finite trace statements, not an unproved positivity assertion supplied
as a field of a structure.

The odd-sector comparison also gives actual native `Matrix.PosSemidef`
conclusions: `A * A` is positive semidefinite for an odd Krein-skew matrix,
and `-(A * A)` is positive semidefinite for an odd Krein-self matrix. An odd
matrix that is both Krein-skew and transpose-skew is zero. These statements
do not claim existence, growth, periodicity or stability of a flow.

### 3. Ordered metric transport

For an invertible real frame `g`, distinguish the pullback `gᵀ H g` from the
metric transported with the inverse frame `(g⁻¹)ᵀ H g⁻¹`. Pulling back the
latter by `g` recovers `H`. The relative operator `J_H(g) g` satisfies
`H (J_H(g) g) = gᵀ H g`; it is not itself the Gram matrix. The associated
weighted adjoint must transform compatibly with conjugation of operators.

For orthogonal `g` and a symmetric involution `η`, the transported matrix
reduces to `g η gᵀ` and remains a symmetric involution. A general invertible
congruence preserves a nondegenerate bilinear form's transport, but need not
preserve the normalization `η² = 1` relative to the original transpose.

### 4. A real logarithm without density positivity

`Examples/RealKreinDensityCounterexample.lean` uses the existing real
`Physics.chiralGrading = diag(1,-1)` and the concrete matrices

\[
N=\begin{pmatrix}2&2\\-2&-2\end{pmatrix},\qquad
\rho=I+N=\begin{pmatrix}3&2\\-2&-1\end{pmatrix}.
\]

It gives proofs of `N * N = 0`, `N ≠ 0`, native metric self-adjointness of
`ρ`, trace two, determinant one, and the negative native bilinear value
`ρ.toBilin' ![0,1] ![0,1] = -1`. The failure of positivity is stated as
`¬ ρ.PosSemidef`, not merely as a comment about its entries.

The generic `realMatrix_exp_of_sq_zero` truncates the actual
`NormedSpace.exp` series for any finite real matrix with square zero. Its
application proves `NormedSpace.exp N = ρ`. Thus the example supplies a real
logarithm witness while refuting positivity. It does not construct a principal
matrix-logarithm function, a symmetric logarithm or a normalized state.

## Implemented dependency order

The proof dependencies, rather than the intake's proposed fifteen-element
diagram, order the formalization:

1. The existing weighted adjoint and unit cancellation give the relative
   commutator criterion; the native matrix-center theorem gives scalar and
   sign recovery.
2. Actual conjugation parity and its projections give the adjoint/transpose
   comparison. That comparison gives the odd-generator square statements.
3. The comparison gives arbitrary-weight trace reciprocity; conjugation
   multiplicativity and cyclic trace give parity invariance. Invariance gives
   both mixed-parity zero identities and then the signed quadratic split.
4. Native Gram positivity gives strict unweighted signs, with nonzero
   hypotheses stated explicitly.
5. The existing ordered matrix change-of-basis theorem gives covariance of
   the unit-valued weighted adjoint. Native bilinear pullback gives vector
   pairing preservation, and unit laws give the relative inverse formula.
6. Native matrix arithmetic supplies the counterexample; square-zero powers
   truncate the analytic exponential series and yield its real logarithm.

The five mathematical owners contain 57 added explicit theorem declarations
and 8 added definitions. This is a source inventory, not the native audit's
count of generated declarations. The selected source closure contains twelve
repository modules. Exact verification status is recorded in
[`REAL_KREIN_CARTAN_VERIFICATION.md`](REAL_KREIN_CARTAN_VERIFICATION.md).

## Corrections and boundaries

| Intake claim | Exact disposition |
|---|---|
| A single adjoint contains “zero” information about its metric. | Overstrong with a fixed reference transpose: the full adjoint map recovers the matrix weight up to a nonzero scalar. |
| The two adjoints recover a unique normalized `η`. | They recover its conjugation action; `η` and `-η` induce the same adjoint. The normalized matrix recovery theorem leaves exactly this sign. |
| An odd Krein-skew generator is transpose-symmetric; an odd transpose-skew generator is Krein-self-adjoint. | Algebraic parity consequences. Any dynamical interpretation additionally needs a defined flow and the relevant analytic theorem. |
| Every skew generator has a periodic flow. | Orthogonality/boundedness does not imply a common period. In several invariant planes, frequencies can be incommensurable. A specified square relation or commensurability hypothesis is needed. |
| A nonzero symmetric generator makes every vector grow. | Overstrong: kernels and decaying eigendirections must be considered. No universal “runaway” claim is promoted. |
| `exp(sY†) exp(sY)` is the moving Gram matrix. | It is a relative operator. The Gram matrix includes the metric factor; inverse-frame transport has its own ordered formula. |
| Krein self-adjointness with positive trace and determinant makes a positive density. | False. The unipotent example in the input is nonsymmetric for nonzero parameter. A faithful real density requires symmetric positive-definiteness. |
| Nonreal eigenvalues, or a nilpotent Jordan defect, prevent a real logarithm. | False. A real plane rotation has the real logarithm `θ J`, where `J² = -I`; if `N² = 0`, then `exp(N) = I + N`. A real logarithm need not be symmetric or a valid positive-state modular Hamiltonian. |
| The two-weight kernel is already the density-coordinate entropy Hessian. | Not identified here. The Bogoliubov covariance kernel on observables and the derivative of the matrix logarithm on density directions require an explicit tangent-variable map. |
| Pointwise reciprocity proves the full BKM metric and its positivity. | The pointwise result precedes functional calculus, integrability and integral positivity. An integral with `ρ`-powers needs those additional owners and hypotheses. |
| Faithfulness implies a bounded logarithm in infinite dimensions. | A positive lower spectral bound is additionally required; the finite-dimensional statement does not establish that bound in a completion. |
| The Cartan symmetric space has strictly negative curvature. | Higher-rank spaces have flat directions. No curvature or classification claim is inferred from the matrix identities. |
| A chosen ranked causal diagram proves a unique physical synthesis or a colimit. | It does not. Only actual Lean dependencies are ordered; no physical uniqueness, holonomy, categorical colimit or analytic convergence is asserted. |
| Hestenes reversion and observer conjugation equal the two operator adjoints. | Requires a specified Clifford representation, scalar-part pairing and sign conventions. The real matrix theorems do not supply this representation theorem. |

## Verification and publication record

At contract creation the source candidates have not been kernel checked.
Local preflight found the maintained shared build lock occupied by another
`clifford-dirac` transaction, so no concurrent compiler or cache process was
started. Verification must use the maintained source-closure checker and its
native declaration axiom audit against the exact pins. Source scans and
independent mathematical review are recorded separately from compilation.

The root Lake workspace has separate dependency/integration requirements;
the source-closure check is not a full repository build. The upstream PR is
published as a draft until its exact-head native results and the outstanding
root-workspace status have been reviewed.
