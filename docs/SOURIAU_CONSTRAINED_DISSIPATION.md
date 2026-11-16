# Souriau thermodynamics, constrained dissipation, and Landauer: theorem contract

Date: 2026-11-16. Base: `08c34e03f610b452e03422037949196dc7d92d6d`
in `nickgou-nuke/info-geometry-lean`.

## Intended result

The input proposes identifying a split-spinor para-Kähler potential with the
Massieu potential, deriving metriplectic dissipation from vacuum-volume
deformation, and obtaining Landauer's bound as a geometric identity. Several
of these identifications require correction or additional models. This change
constructs the missing **energy-constrained noncommutative mobility** on the
existing completed GNS carrier. It preserves the original order of all
operator products.

The original intake is preserved in
`docs/SOURIAU_METRIPLECTIC_LANDAUER_INTAKE_20261116.md`.

This is a bounded analytic/operator theorem contract. It does not claim a
physical vacuum model, a quantum entropy evolution equation, a density-matrix
preserving semigroup, or a derivation of Landauer heat from volume.

## 1. Source-grounded claim ledger

| Input claim | Disposition | Existing owner or missing implication |
|---|---|---|
| A split structure has an involution and isotropic halves | Valid with the specified pairing and compatible splitting | `Geometry/ParaHessianMixedPotential.lean` and the para-Kähler owners; a spinor interpretation additionally needs a Clifford representation and invariant pairing |
| A Massieu potential is automatically the para-Kähler potential | Additional construction required | A positive Hessian can be induced on a Lagrangian graph in a doubled neutral space; it is not the ambient neutral metric |
| `mu = D log Z` with the negative Gibbs exponential | Incorrect sign | `Canonical/CartanSouriauMassieuDirectionalCalculus.lean` proves the negative mean readout in affine natural parameters |
| `S = beta mu - log Z` for that same convention | Incorrect sign | The dimensionless Gibbs entropy is `log Z + beta mu` |
| Every equilibrium is parameterized by one coadjoint orbit | Overstrong | The Gibbs family has an admissible parameter domain; orbit covariance is a separate theorem with action/cocycle hypotheses |
| The Fisher metric equals the neutral para-Kähler metric | False on the same nonzero tangent space | `Canonical/SouriauOnsagerBKMParaKahlerObstruction.lean` proves the strict-positive BKM obstruction |
| GENERIC conserves energy and produces entropy | Conditional on its structural degeneracies | `Thermo/GenericMetriplecticFlow.lean` already proves both rate laws and the injective-Poisson obstruction |
| An arbitrary positive commutator Laplacian conserves the chosen energy | Missing constraint | This change projects away the energy direction before forming the Dirichlet sum of squares |
| Local volume deformation determines the metric bracket | Unsupported | A scalar divergence does not determine a symmetric positive operator or its kernel |
| Landauer is an exact vacuum-volume identity | Unsupported | The exact quantum identity involves erased entropy, final correlations, and relative entropy of a specified reservoir |

### Existing owners reused

- `Analysis/OperatorDirichletLaplacian.lean` constructs the actual bounded
  operator `laplacian T = sum_i (T i)* (T i)` and proves its energy, positivity,
  kernel, and precomposition identities.
- `OperatorAlgebra/TracialGNSRightMultiplication.lean` and
  `OperatorAlgebra/TracialGNSCommutator.lean` construct the right action and
  inner commutators on the completed native GNS space.
- `OperatorAlgebra/TracialGNSDirichlet.lean` constructs their Dirichlet operator
  and identifies its kernel with the joint commutant on faithful dense
  representatives.
- Mathlib's closed-submodule orthogonal projection supplies the actual
  constraint map. Positivity and the energy-kernel equation are conclusions
  of the construction, not fields storing the requested result.

The bounded owner search also inspected the full-matrix double-commutator
owner, GENERIC consumers, CE/BKM Onsager owners, finite Gibbs entropy owners,
para-Hessian compatibility, log-Jacobian owners, and Landauer-named modules.
This is not a claim that every file in the repository was compiled.

## 2. Mathematical contract

Let `E` and `F` be complex Hilbert spaces and let `T_i : E ->L[ℂ] F` be a
finite family of bounded maps. The Hilbert spaces may be infinite dimensional;
the finite restriction is on the index set of maps.

For the specified energy direction `h`, let `K_h = (span ℂ {h})ᗮ` and let
`P_h` be its actual orthogonal projection. The implemented construction is

\[
 M_{T,h}=\sum_i(T_iP_h)^*(T_iP_h)=P_h\Delta_TP_h,
 \qquad \Delta_T=\sum_iT_i^*T_i.
\]

The acceptance targets are:

1. `M` is self-adjoint and positive.
2. Its real quadratic form is exactly `sum_i ||T_i(P_h s)||^2`.
3. Its zero quadratic form, operator kernel, and simultaneous vanishing of
   `T_i(P_h s)` are equivalent.
4. The specified energy direction `h` is annihilated by `M`, and
   `Re <h, M s> = 0` for every `s`.
5. Choosing `K_h = (span ℂ {h})ᗮ` constructs an energy constraint for every `h`,
   including `h = 0`, without dividing by a possibly zero norm.
6. With a supplied skew-adjoint reversible operator `J` satisfying `J s = 0`,
   the pointwise velocity `v = J h + M s` obeys
   `Re <h,v> = 0` and `Re <s,v> = sum_i ||T_i(P_h s)||^2`.

Here `h` and `s` are force vectors. Interpreting them as gradients of actual
energy and entropy functionals is additional model data. The reversible
operator's skewness and entropy-Casimir equation are explicit hypotheses;
they do not assert a Poisson Jacobi identity or solve an evolution equation.

### Noncommutative specialization

Let `A` be a possibly nonunital C*-algebra and let `f : A ->ₚ[ℂ] ℂ` be a
positive tracial functional. On its completed `f.GNS`, use the already-owned
bounded maps

\[
 T_i[a]=[H_i a-aH_i].
\]

There is no assumption that the `H_i` commute, are diagonal, or are
self-adjoint. Adjoint compositions provide positivity even for general
`H_i`.

The compressed operator then has the exact energy

\[
 \operatorname{Re}\langle s,M s\rangle
 =\sum_i\|T_i(P_hs)\|^2.
\]

For `h = [e]` and `s = [a]`, the projection has a proved dense coefficient
representative

\[
 a_\perp=a-\frac{f(e^*a)}{f(e^*e)}e,
 \qquad P_{[e]}[a]=[a_\perp].
\]

The formula also covers a zero GNS energy vector, using native zero inverse.
The energy identity becomes

\[
 \sum_i\operatorname{Re}f\bigl([H_i,a_\perp]^*[H_i,a_\perp]\bigr).
\]

Faithfulness on positive squares is needed only to conclude that zero
production means each algebra commutator itself vanishes. Without
faithfulness the exact statement concerns GNS null classes.

This uses the repository's existing complex C*-GNS carrier. The observable
rates are real parts of Hilbert pairings. No scalar imaginary unit is inserted
to replace an operator, and no change to the real para-Kähler carrier is
asserted. The projection removes the whole complex line through `h`; this is
a stronger constraint than removing only its underlying real line.

### Actual dependency order

1. Positive tracial functional -> completed GNS carrier and bounded left/right
   actions.
2. Ordered left-minus-right action -> bounded inner commutator family.
3. Specified energy direction -> projection onto its complex orthogonal complement.
4. Commutators composed with the projection -> adjoint sum of squares.
5. That sum -> positivity, exact kernel, and the energy degeneracy.
6. Additional reversible degeneracy -> the two pointwise rate identities.

There is no proved dependency arrow from this construction to physical
vacuum expansion or the Landauer reservoir theorem.

## 3. Correct thermodynamic conventions

Use dimensionless entropy `s = S/k_B`. For a Hamiltonian group action with
moment map `J`, fix the negative exponential convention

\[
 Z(\beta)=\int e^{-\langle\beta,J(x)\rangle}\,d\lambda_\omega(x),
 \quad \Psi=\log Z,\quad
 p_\beta=Z^{-1}e^{-\langle\beta,J\rangle}.
\]

Where the integral and differentiations exist,

\[
 \mu=-D\Psi,\qquad s=\Psi+\langle\beta,\mu\rangle,
 \qquad s(\mu)=-\Psi^*(-\mu).
\]

The last equality uses attainment at the matching dual coordinate. For two
equiprobable states at `beta = 0`, both `Psi` and `s` equal `log 2`; the
intake's entropy formula would instead give `-log 2`. Marle proves the Gibbs
identities and their admissibility hypotheses [1].

The covariance-Hessian formula uses **affine natural parameters**. The
repository's older `(beta, chemicalPotential)` coordinate chart has exponent
`-beta * (E - chemicalPotential * N)` and therefore an extra mixed first-moment
term. Its raw coordinate Hessian should not automatically be called the
Fisher metric. The directional Cartan-Souriau owner uses the linear charge
pairing and is the appropriate natural-parameter reference.

For noncommuting quantum charges, write `K_beta = sum_a beta_a Q_a` and
`rho_beta = exp(-K_beta)/Tr(exp(-K_beta))`. The Hessian is the centered
Bogoliubov-Kubo-Mori integral, retaining the order of the operators:

\[
 D^2\Psi_\beta(u,v)=\int_0^1
 \operatorname{Tr}\left(\rho_\beta^t\widetilde Q_u
 \rho_\beta^{1-t}\widetilde Q_v\right)dt.
\]

The repository already has this genuine noncommutative response lane; this
change does not replace it with ordinary commuting covariance [6].

## 4. Compatible para-Kähler geometry

On the real doubled space `V ⊕ V*`, put

\[
 K(v,\alpha)=(v,-\alpha),\qquad
 g((v,\alpha),(w,\gamma))=\alpha(w)+\gamma(v),
\]

\[
 \omega(x,y)=g(Kx,y).
\]

Then `K²=1`, `g(Kx,Ky)=-g(x,y)`, and the two factors are isotropic. With
this convention `g(x,y) = -omega(x,Ky)`. A positive Fisher metric cannot be
the entire neutral form `g` on the same nonzero space.

For a symmetric bilinear form `B`, the graph `i_B(v)=(v,B(v,-))` instead
satisfies the directly calculable identities

\[
 i_B^*\omega=0,\qquad i_B^*g=2B.
\]

Thus the Hessian of a convex Massieu potential can occur as a metric induced
on a spacelike Lagrangian graph, while the ambient metric remains neutral.
Fox describes this doubled geometry [2]. This section is an explanatory
derivation, not a claim that the new constrained-operator modules formalize
the graph construction or a spin representation.

## 5. Volume change and irreversible dynamics

For `Omega_t = exp(sigma(x,t)) Omega_0`, the local relative density is
`exp(sigma)-1`. By the product rule for a Lie derivative,

\[
 (\partial_t+\mathcal L_X)\Omega_t
 =\bigl(\partial_t\sigma+X\sigma+
 \operatorname{div}_{\Omega_0}X\bigr)\Omega_t.
\]

The relative volume change of a region is an integral average of the local
density change. A single scalar divergence cannot specify a positive
dissipative operator or its energy kernel.

A counterexample at the level of the stated GENERIC conditions is
`H(x,y)=x`, `s(x,y)=y`, `L=0`, `M=diag(0,1)`. Its velocity is the constant
translation `(0,1)`, with zero divergence, conserved `H`, and `ds/dt=1`.
This elementary counterexample refutes the universal volume-source inference;
it is not used as a replacement for the noncommutative construction above.

Under full GENERIC degeneracy, an injective reversible Poisson map and
`L ds = 0` force `ds=0`. The repository already proves that obstruction.
Nontrivial macroscopic GENERIC dynamics consequently need a degenerate
Poisson structure or an appropriate extended/reduced state space [3].

## 6. Landauer: the precise remaining theorem

For an initially uncorrelated system and reservoir, let

\[
 \rho_{SR}=\rho_S\otimes\tau_R,\qquad
 \tau_R=\frac{e^{-\sum_a\beta_aQ_a}}{Z},\qquad
 \rho'_{SR}=U\rho_{SR}U^*.
\]

Define `Delta q_a = Tr(Q_a(rho'_R-tau_R))` and
`Delta s_S = s(rho'_S)-s(rho_S)`. The relative-entropy calculation gives

\[
 \sum_a\beta_a\Delta q_a
 =-\Delta s_S+I(S:R)_{\rho'}+D(\rho'_R\Vert\tau_R)
 \ge -\Delta s_S.
\]

Reeb and Wolf prove the one-charge thermal equality under explicit reservoir,
initial-product, and unitary hypotheses [4]. The displayed multiple-charge
version follows from the same entropy calculation and
`-log(tau_R)=sum_a beta_a Q_a + log Z`; pairwise commutation of the charges
is not required. Multiple noncommuting charges and their weighted tradeoffs
are treated by Guryanova et al. [5].

For a thermal reservoir `beta=1/(k_B T)`, perfect erasure of an initially
unbiased bit gives the lower bound `Q >= k_B T log 2`. Attainability is a
separate issue; finite reservoirs and imperfect erasure require their stated
qualifications. The equality accounts for excess cost through correlations
and reservoir relative entropy, without asserting local vacuum expansion.

The inspected Landauer-named owners define cost formulas and prove their
arithmetic consequences. They do not supply this reservoir derivation. This
change leaves that physical/quantum-information theorem explicit rather than
assuming its entropy balance as a new structure field.

## 7. Verification and publication scope

The independent fresh source-closure rerun passed. All six repository modules
in the import closure compiled with zero warnings and no reused repository
artifacts. The native declaration audit covered 154 declarations, including
generated declarations; 44 belong to the two new modules. Their transitive
axiom dependencies are limited to `propext`, `Classical.choice`, and
`Quot.sound`. The two final source hashes also received an independent
semantic-review PASS.

The strict placeholder scan found no hard findings. It flagged the positive
functional `f` and traciality hypothesis `htr` as two soft hypothesis-review
items; both are explicit input assumptions described above. Semantic-vacuity,
OpenGauss screening, and refutation checks found no issues. Gate 4 source
review passed; its own result is explicitly static, while the separate
source-closure run supplies the kernel check.

The exact source-closure command, with local paths replaced by placeholders,
is:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /absolute/path/to/pinned-mathlib \
  --lean /absolute/path/to/lean-4.34.1/bin/lean \
  --output /absolute/path/to/fresh-verification \
  --target InfoGeometry.Analysis.OperatorDirichletLaplacian \
  --target InfoGeometry.Analysis.ConstrainedDirichletLaplacian \
  --target InfoGeometry.OperatorAlgebra.TracialGNSRightMultiplication \
  --target InfoGeometry.OperatorAlgebra.TracialGNSCommutator \
  --target InfoGeometry.OperatorAlgebra.TracialGNSDirichlet \
  --target InfoGeometry.OperatorAlgebra.TracialGNSConstrainedDirichlet
```

The delivery package preserves the complete source snapshot, compiler and
axiom logs, source hashes, static-gate commands/results, and independent
semantic review. This verifies the declared bounded-operator result and its
import closure, not every file in the repository.

Both maintained root-integration probes were also run:

```bash
python3 tools/infra/run_locked_lean.py \
  --lake /absolute/path/to/lean-4.34.1/bin/lake \
  lean/InfoGeometry/OperatorAlgebra/TracialGNSConstrainedDirichlet.lean
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock --wfail \
  InfoGeometry.OperatorAlgebra.TracialGNSConstrainedDirichlet
```

Both exited with code 1 during dependency resolution because the configured
path dependency `external_refs/homotopy-hypothesis-lean4` is absent from this
checkout. They did not reach compilation of the new modules. The exact-pin
source-closure check above remains valid independently of that root Lake
setup failure. No repository-wide build success or upstream publication is
claimed. The work is delivered as a local feature-branch commit and patch.

Pinned environment: Lean `v4.34.1`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. No dependency pins are changed.

## References

1. C.-M. Marle, *On Gibbs States of Mechanical Systems with Symmetries*,
   JGSP 57 (2020), especially Propositions 3.2.2–3.2.3.
   <https://marle.perso.math.cnrs.fr/pdffiles/2020/GibbsStatesJGSPPart1.pdf>
2. D. J. F. Fox, *Einstein-like Geometric Structures on Surfaces* (2013),
   discussion of the cotangent para-Kähler structure and Hessian graphs.
   <https://www.numdam.org/item/ASNSP_2013_5_12_3_499_0.pdf>
3. P. J. Morrison and M. H. Updike, *Metriplectic 4-bracket Dynamics*.
   <https://arxiv.org/abs/2306.06787>
4. D. Reeb and M. M. Wolf, *An Improved Landauer Principle with Finite-size
   Corrections*, Theorem 3. <https://arxiv.org/abs/1306.4352>
5. Y. Guryanova et al., *Thermodynamics of Quantum Systems with Multiple
   Conserved Quantities*. <https://arxiv.org/abs/1512.01190>
6. P. Abiuso et al., *Geometric Optimisation of Quantum Thermodynamic
   Processes*, Entropy 22 (2020), 1076.
   <https://pmc.ncbi.nlm.nih.gov/articles/PMC7597153/>
