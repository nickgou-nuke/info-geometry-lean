# Real BKM constraints and squared-associator dissipation

## Source, scope, and acceptance

This continuation processes the two user notes preserved byte for byte in
`docs/intake/real-bkm-associator-20261117/`. The manifest records their original
names, byte counts, and SHA-256 hashes. Mathematical and verification claims
inside the notes are input to the audit, not evidence of acceptance.

The development repository is `nickgou-nuke/info-geometry-lean`, based on
`08c34e03f610b452e03422037949196dc7d92d6d`. The separate Yang--Mills submission
snapshot is unchanged. This task uses an independent sparse checkout with a
real `.git` directory. No dependency pin, shared build lock, existing gate, or
root Lake configuration is changed.

The deliverable constructs real bilinear projections and positive Gram forms
on the actual full matrix and split-octonion carriers. Its algebraic statements
are pointwise. Existence of a trajectory, preservation of the density cone,
Jacobi for a state-dependent Poisson tensor, and convergence need additional
analytic proofs. Current execution evidence is recorded in
`REAL_BKM_ASSOCIATOR_VALIDATION.md`.

## Structural motifs translated into mathematics

| Motif | Precise object | Required implication |
|---|---|---|
| Normalization | A real vector `e` with `B(e,e)=1` | `C(x)=x-B(e,x)e` removes precisely the scalar direction. |
| Independent energy | An energy `H` outside `span {e}` | Strict positivity gives `B(CH,CH)>0`, so the second Gram coefficient is defined without a zero denominator. |
| Constrained residual | The native linear map `P(x)=C(x)-beta(x)CH` | Both normal equations hold; its kernel is `span {e,H}` and its range is the native bilinear orthogonal complement. |
| Noncommutation | The ordered difference `xH-Hx` in an associative real algebra | Subtracting `alpha*1+beta*H` preserves this entire difference. |
| Positive observation | A positive definite real form | A nonzero residual has positive quadratic response; an indefinite Krein form is not used for this implication. |
| Failure of associativity | The actual map `v ↦ (v*a)*b-v*(a*b)` on split octonions | Compositions of linear maps give a native linear leakage operator while retaining the nonassociative product. |
| Dissipation | A finite sum of positive Gram pullbacks | Energy annihilation follows from the projection; zero response means membership in the common leakage kernel. |
| Equilibrium normalization | Zero projected surprisal plus a normalized faithful state | The Gram intercept can then be identified with the Gibbs log-partition value. |

The dependency order is supplied by these maps and proofs. Naming a terminal
node in a finite narrative graph neither constructs a universal property nor
proves uniqueness of a physical theory.

## Existing owners inspected and reused

| Existing owner | Actual content | Decision |
|---|---|---|
| `Canonical.KuboMoriBogoliubovMetric` | Positive normalized real eigenvalues; logarithmic-mean weights; a pairing on **all** `Matrix n n ℝ`; symmetry; nonnegativity conditional on supplied weight signs | Discharge every weight sign, package a native bilinear form, and prove strict positivity. |
| `Canonical.BKMScalarGaugeQuotient` and `NoncommutativeGibbsCenteredBKMCovariance` | Genuine centering and scalar quotient for the existing complex operator carrier viewed as a real module | Useful precedent, but their carrier is not silently presented as a real matrix algebra. |
| `Canonical.SouriauOnsagerBKMBridge` and `SouriauOnsagerBKMRealForm` | Complex bounded operators with real bilinear restriction | No complex-only realization is substituted for the requested real construction. |
| Native `BilinearForm.Orthogonal`, `Projection`, and submodule spans | Orthogonal complements, native `LinearMap.IsProj`, kernels, ranges, and complements | Reuse these types rather than introduce another projector structure. |
| `Algebra.MatrixNoncommutativity` | A shared real symmetric pair with a closed noncommutativity proof | Reuse the actual full matrices for a positive-response witness. |
| Native `Unitary.conjStarAlgAut` | Multiplicative, star-preserving conjugation by a unitary element | On real matrices this supplies an orthogonal change of frame. |
| `Canonical.SplitOctonionRegularOperators` | Real quaternion-pair split octonions and native left/right multiplication endomorphisms | Form the exact ordered associator from the existing right-regular maps. |
| `Canonical.SplitOctonionBogoliubovCarrierBridge` | Linear equivalence of the full real split-octonion carrier with the doubled quaternionic Hilbert carrier | Pull back the existing positive observer form. This is a linear identification, not an associative algebra isomorphism. |
| `Geometry.ParaHessianMixedPotential` | Actual Fréchet derivative, gradient, and Hessian for a mixed cross potential; neutral metric and symplectic nondegeneracy | Reuse as the existing potential owner; do not duplicate it. |
| `Lie.SplitOctonionParaHessianBridge` | Transport to an active Zorn `3+3` carrier | Do not report that result as an already-proved full eight-dimensional curved metric. |
| `Thermo.GenericMetriplecticFlow` | State/covector system, energy and entropy rates, and the obstruction from an injective reversible operator | Retain the distinction between a positive response and a complete dynamical system. |
| `Thermo.BilinearMetriplecticReduction` | Native inverse-duality congruence construction and its exact kernel | No duplicate Riesz or GENERIC structure is introduced. |

Search covered owner definitions, alternate names and representations, imports,
and direct consumers. Searches in source and maintained routing documentation
are bounded evidence; no live Arango/DAG database freshness is claimed.

The referenced [PR #371](https://github.com/nickgou-nuke/info-geometry-lean/pull/371)
is an independent draft. Its scoped run
[44047439184](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44047439184)
is now successful; the attached note's queued status is stale. Its CAR and
crossed-product results alone supply neither a neutral bilinear form nor a
split-octonion tensor representation.

## Contract A: the real Kubo--Mori response

Let `rho : KuboMoriBogoliubov.FaithfulDensityState n`. Its supplied fields are
`p_i>0` and `sum_i p_i=1`. The carrier of observables is the full associative
real algebra `Matrix n n ℝ`. The density is described in spectral coordinates;
the observables are arbitrary matrices in that basis.

The logarithmic-mean weight is

\[
L(p,q)=\begin{cases}p,&p=q,\\
\dfrac{p-q}{\log p-\log q},&p\ne q.
\end{cases}
\]

Strict monotonicity of the real logarithm proves `L(p,q)>0`. Therefore

\[
B_\rho(A,B)=\sum_{i,j}A_{ji}B_{ji}L(p_i,p_j)
\]

is symmetric and strictly positive on every nonzero real matrix. Identity
insertion is `sum_i p_i A_ii`, and `B_rho(1,1)=1`. These conclusions are derived;
off-diagonal weight positivity is no longer a supplied hypothesis.

The scalar interpolation and the full ordered trace integral are identified:

\[
L(p,q)=\int_0^1 p^{1-t}q^t\,dt,
\qquad
B_\rho(A,B)=\int_0^1
\operatorname{tr}\bigl(\rho^{1-t}A^\mathsf T\rho^tB\bigr)\,dt.
\]

The Lean density powers in this formula are the actual diagonal matrices of
positive real powers. All entries of `A` and `B` remain present. The additional
frame construction uses the inverse of the native conjugation equivalence:
`B_U(A,B)=B_rho(U^T A U,U^T B U)` for a real orthogonal matrix `U`. It preserves
strict positivity and normalized identity. It is not a restriction to simultaneously diagonal
observables. An automatic spectral decomposition of an arbitrary supplied
positive matrix is not part of this owner.

This is the Kubo--Mori response on observable/covector directions. Identifying
it directly with the density-tangent metric would miss the inverse response
operator. Likewise, this file does not re-prove the full Gibbs log-partition
Fréchet Hessian or a physical choice of state dynamics.

## Contract B: the two normal equations

For `B : LinearMap.BilinForm ℝ V`, a normalized `e`, and energy `H`, set

\[
Cx=x-B(e,x)e,\qquad
\beta(x)=\frac{B(CH,Cx)}{B(CH,CH)},\qquad
\alpha(x)=B(e,x)-\beta(x)B(e,H).
\]

The constructed endomorphism is

\[
Px=Cx-\beta(x)CH=x-\alpha(x)e-\beta(x)H.
\]

Under `B(e,e)=1` and the nonzero centered-energy denominator, prove:

- `B(e,Px)=B(H,Px)=0` and `P(e)=P(H)=0`;
- `P` is a native projection and is idempotent;
- `ker P = span {e,H}` and `range P = B.orthogonal (span {e,H})`;
- the constraint space and its indicated right orthogonal complement are
  complementary, without a finite-dimensional assumption;
- symmetry of `B` makes `P` self-adjoint;
- `D(x,y)=B(Px,Py)=B(x,Py)`;
- positive semidefiniteness descends to `D`, and strict positivity of `B`
  gives `D(x,x)=0` exactly when `x` lies in the constraint span.

The construction weakens hypotheses where the proof permits it. The two normal
equations and kernel/range results do not require symmetry; self-adjointness
does. The denominator is derived from strict positivity and nonscalar energy.
The definition itself is total even at a zero denominator, but the normal
equation and exact kernel contracts retain their stated denominator hypothesis.

For the real matrix specialization `e=1`, ordered multiplication gives

\[
[Px,H]=[x,H].
\]

Hence noncommutation implies nonzero projected force and strictly positive BKM
response. The converse is false. The explicit three-level example
`H=diag(0,1,2)`, `x=diag(1,0,0)` commutes but lies outside `span {1,H}`, so its
constrained response is positive for every faithful spectral density. Particular
diagonal witnesses do not restrict the ambient theorem's full matrix carrier.

The actual spectral surprisal is `diag(-log p_i)`. It commutes with its own
density at every faithful state, independently of equilibrium. Its projected
force has the coefficients and normal equations above. These pointwise results
do not by themselves construct `dot rho` or a positive-cone-preserving ODE.

## Contract C: positive associator dissipation

For a finite family of native real endomorphisms `R_i`, a native linear map `P`,
a symmetric observer form `B` with nonnegative diagonal, and `gamma>=0`, construct

\[
G(x,y)=\gamma\sum_i B(R_iPx,R_iPy).
\]

Prove symmetry and nonnegativity, and annihilation in both slots of every
`H` with `PH=0`. When `gamma>0` and `B` is strictly positive,

\[
G(x,x)=0\iff\forall i,\ R_iPx=0,
\qquad
\ker G=\bigcap_i\ker(R_i\circ P).
\]

Strict positivity is equivalent to at least one active leakage mode. Equality
with `ker P` needs an additional joint-separation hypothesis on `range P`.
That hypothesis is not silently inferred from nonassociativity.

The concrete carrier is the existing full split-octonion algebra
`Quaternion ℝ × Quaternion ℝ`, with its existing nonassociative multiplication.
The observer form is pulled back from the existing positive doubled Hilbert
form. The ordered operator

\[
R_{a,b}=\operatorname{rightRegular}(b)\circ
\operatorname{rightRegular}(a)-\operatorname{rightRegular}(ab)
\]

evaluates to `(v*a)*b-v*(a*b)`. A component of a positive Gram form is built from
this actual associator, not from a numerical proxy for it.

For the closed example take the exact energy-orthogonal projection
`P(v)=v-B(1,v)*1`, with `B(1,1)=1`, and the split-octonion units `ell`, `i*ell`,
and `j`. The existing multiplication gives `[ell,i*ell,j]=-2k`. For the
singleton family with fixed arguments `i*ell,j` and coefficient `gamma=1`,
the quadratic response at `ell` is exactly `4`. The energy direction `1` is
annihilated. The kernel of this projection is exactly `span {1}`. The same
nonzero leakage family has zero response at `i*ell`, although
`P(i*ell)=i*ell` is nonzero. Left alternativity proves this stationary
counterexample; it shows why the additional separation hypothesis is necessary.

The associative limit is stated only when all three associator arguments
belong to a common subset on which multiplication is associative. A projected
vector lying in a quaternionic subalgebra does not suffice if the two fixed
associator arguments are outside it.

## Contract D: Gibbs normalization at zero residual

The finite spectral surprisal satisfies the actual matrix-exponential identity

\[
\exp(-I_\rho)=\operatorname{diag}(p_i).
\]

If its normal decomposition has zero residual, then
`I_rho = alpha*1 + beta*H`. The scalar identity commutes with every real
matrix, so the native commuting-exponential theorem gives

\[
\operatorname{diag}(p_i)=e^{-\alpha}\exp(-\beta H).
\]

Taking the trace and using the state's supplied normalization proves

\[
Z=\operatorname{tr}(\exp(-\beta H))=e^\alpha>0,\qquad
\alpha=\log Z,\qquad
\operatorname{diag}(p_i)=Z^{-1}\exp(-\beta H).
\]

These are conclusions of `normalized_gibbs_of_constrainedSurprisal_eq_zero`,
not assumptions defining an equilibrium record. The theorem holds for an
arbitrary full real matrix `H` satisfying the zero-residual premise; it does
not assume that all observables commute. This implication does not require
nonscalar energy: that hypothesis belongs to the projection's exact two-
constraint normal-equation and kernel theorems. The Gibbs result is a
pointwise stationarity implication, not a construction of a convergent flow
or a claim that the off-equilibrium Gram intercept normalizes an exponential.

## Corrections and remaining mathematical obligations

1. **Gram intercept and Gibbs normalization.** Away from equilibrium,
   `alpha=B(1,I)-beta*B(1,H)` is the intercept of a normal equation. It is not
   generally `log Z(beta)`, and this projected residual is not generally the
   surprisal difference from the energy-matched Gibbs state. The Gibbs
   normalization identification is established under the zero-residual
   premise in Contract D.
2. **Single versus two generators.** With both degeneracy laws, choosing
   the same observable for energy and entropy kills both contributions.
   Distinct generators alone do not guarantee nonzero dynamics.
3. **Symplectic-Casimir obstruction.** Requiring `{F,S}=0` for every `F` on
   a nondegenerate symplectic carrier forces `dS=0`. The weaker equation
   `{S,H}=0` for one Hamiltonian does not establish the full Casimir law.
   A nontrivial metriplectic model needs appropriate degeneracy or an enlarged
   state space; the existing GENERIC owner already proves the injective case.
4. **Strict entropy production and leaves.** It excludes a velocity tangent
   to an entropy-constant orbit. It does not prove global entry into a chosen
   convex hull, declining purity, a geodesic equation, or convergence.
5. **Gibbs domains.** Finiteness, normal local convergence, openness, and
   conicity are different properties. Souriau's regular domain is defined by
   normal local convergence and is open and convex. There is no general
   restriction to a chosen compact `so(4)` subalgebra. The measure, moment map,
   and tails must be specified. Strict Hessian positivity and a global Legendre
   diffeomorphism require appropriate nondegeneracy and global hypotheses.
6. **Faithfulness and infinite dimension.** Finite positive eigenvalues make
   this surprisal finite. An infinite-dimensional faithful trace-class state
   need not have a bounded logarithm or a uniformly positive spectral gap.
   Lean's total real logarithm at zero is not an infinity-valued boundary model.
7. **Real state dynamics.** The commutator of two real symmetric matrices is
   skew-symmetric. Writing `dot rho=[H,rho]` with symmetric `H` therefore does
   not define a tangent vector to the real symmetric state manifold unless the
   commutator vanishes. A skew
   generator or a constructed internal complex structure is needed.
8. **Tensor carrier.** An external representation can act associatively on
   the first tensor factor while the internal split-octonion multiplication
   remains nonassociative. A real linear identification with an eight-dimensional
   Clifford carrier is not an algebra isomorphism, and a tensor product is not
   the uniquely forced representation construction.
9. **Cross potential.** Antisymmetrizing a symmetric real pairing gives zero.
   The mixed cross potential has a nonzero mixed Hessian; the flat potential
   has zero pure `xx` Hessian. Neither observation proves a curved
   Monge--Ampere solution. Ricci signs and factors must be fixed from the
   chosen metric and curvature conventions before a curvature identity is
   promoted.
10. **Landauer and convergence.** Positive Gram response proves neither a
    heat/entropy equality nor a per-bit heat lower bound. A bath model,
    temperature convention, entropy units, erasure protocol, and dynamical
    hypotheses are missing. Unique asymptotic Gibbs convergence is likewise
    not a consequence of the sign of an instantaneous quadratic response.
11. **Souriau cocycle identity.** The displayed identity needs the actual
    Hamiltonian action, affine moment-map equivariance, differentiability,
    and sign convention. It is not proved for an arbitrary independently
    supplied cocycle by the projection construction.
12. **Proof status.** A source scan, native compilation, transitive axiom
    audit, mathematical review, and whole-repository integration are separate
    checks. The raw notes' claims of a completed unique synthesis do not
    discharge any of them.

## Primary mathematical references

- Charles-Michel Marle, [On Gibbs states of mechanical systems with symmetries](https://marle.perso.math.cnrs.fr/pdffiles/2020/GibbsStatesJGSPPart1.pdf),
  Definition 3.1.2 and Proposition 3.1.3, for normal local convergence and the
  regular open convex temperature domain.
- Philip J. Morrison and Michael H. Updike,
  [Inclusive curvaturelike framework for describing dissipation: Metriplectic 4-bracket dynamics](https://web2.ph.utexas.edu/~morrison/24Morrison_Updike.pdf),
  Physical Review E 109, 045202 (2024), for the distinct Hamiltonian/entropy
  generators and degenerate dissipative construction.
- Yann Thanwerdas and Xavier Pennec,
  [O(n)-invariant Riemannian metrics on SPD matrices](https://arxiv.org/abs/2109.05768),
  for real positive-matrix geometry and the distinction between a metric and
  its cometric. The Lean trace-integral and positivity claims above are checked
  from their exact source, not certified by these references.

## Validation contract

Preserve Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Compile the complete owned import
closure of every new target under the maintained shared lock. Run the maintained
native declaration audit over every constant owned by the targets, including
private/generated declarations. Require zero compiler warnings in the new
owners, and reject dependencies beyond `propext`, `Classical.choice`, and
`Quot.sound`. Run the existing strict placeholder, semantic-vacuity, staged
proof, and whitespace checks at their stated scopes. Do not weaken a root gate
or silently repair an unrelated baseline file to manufacture acceptance.
