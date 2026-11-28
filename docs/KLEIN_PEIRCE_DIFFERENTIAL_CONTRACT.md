# Continuous odd inner differential on real Klein sections

## Intake and scope

This change extracts a precise continuation of the polarization, odd-square,
and two-sheeted operator-algebra claims in the 2026-11-28 discussion.
Baseline: `e2aa23c786c63c8992e8936346ed5f7782e4e164`. The checked-in native
Lean and Mathlib pins are unchanged.

The carrier is the existing algebra of continuous equivariant fields on the
Klein covering torus, with the full continuous real endomorphism algebra of
`DoubledSpace E` as fibre. `E` is any complete real inner-product space; no
finite-dimensional or commutative restriction is imposed. The topology is the
existing native section topology. The new map is an algebraic graded
differential, with continuity, rather than differentiation in a base direction.

Risk/scope: R4, topological operator-algebra construction using existing
owners. The general square-zero theorem has an explicit central-square
hypothesis. The mirror specialization derives it from the existing square-one
theorem. Physical supersymmetry, positive energy, modular dynamics, and a
base-space curvature tensor are outside this theorem contract.

## Owner search and reuse

- `Core.PeirceGrading` supplies the division-free direct decomposition,
  `commutator_odd`, and all four parity multiplication laws over any `Ring`.
  Its full eigenspace identification separately requires injective doubling.
- `Algebra.DeWittPeirceSuperalgebra` proves the double-commutator soul
  projection and the cubic identity for commutation with a sheet idempotent.
- `OperatorAlgebra.PeirceTwistedComplex` defines `twistedInner` as a native
  `Module.End`, and proves its twisted Leibniz, parity reversal, square, and
  naturality identities. Its existing short-complex constructor assumes the
  generator itself has square zero.
- `Topology.KleinRealKreinPeirceSections` constructs the actual real section
  algebra, continuous grading, deck equivariance, and a concrete odd mirror
  section with square one. `mirror_grading_commute` is the previously
  requested identity `rho Pi = Pi rho`.
- Related algebraic owners include `InvolutiveTwistedDifferential`,
  `IntrinsicGradedAdjoint`, `PeirceSpine.CentralizerDifferential`, and
  `Cl11GradedDifferential`. The last has a contraction on an algebraic
  Clifford colimit, not on this continuous section carrier.

The new file joins existing owners without regenerating their ring identities
or introducing a replacement carrier. Bounded searches of native `lean/` and
`src/` did not find the exact prompt names `bodyFixedSubalgebra`,
`soulFixed_mul_soulFixed`, `commutator_even_pow_bodyFixed`, `stateCentralizer`,
`innerStarDeriv_mem_starKilling_gns`, or `modular_timeSlice_moment_invariant`
at this baseline. This revision-specific observation does not exclude another
branch or workstation source. The substantive owners above were inspected.

## Theorem contract

Write `S = Sections`, `Pi = sectionGrading`, and `J = mirrorSection`.

1. Construct `differential q : S →L[ℝ] S` whose underlying linear map is
   definitionally the existing `LieJordan.twistedInner`:
   `d_q(a) = q*a - Pi(a)*q`.
2. Prove the full pointwise operator formula and actual deck readback. Closure
   is in the equivariant section subalgebra.
3. Reuse `twistedInner_leibniz` to obtain
   `d_q(a*b) = d_q(a)*b + Pi(a)*d_q(b)` for all sections.
4. For `Pi(q) = -q`, prove parity reversal and
   `d_q(d_q(a)) = (q*q)*a - a*(q*q)`.
5. If `q*q` commutes with every section, prove
   `(differential q).comp (differential q) = 0`.
   This is weaker than requiring `q*q = 0`.
6. Specialize to the constructed odd section `J`, for which `J*J = 1`.
   Obtain `mirrorDifferential_square_zero` and, when `Nontrivial E`, a
   nonzero differential through `d_J(J) = 2 • 1`.
7. Construct the continuous map `h(a) = (1/2) • (J*a)` and prove
   `d_J.comp h + h.comp d_J = id`. Consequently every cycle is a boundary:
   `LinearMap.range d_J = LinearMap.ker d_J`.
8. Construct the native `CategoryTheory.ShortComplex (ModuleCat ℝ)` from
   this differential and its proved square-zero identity.

The contraction applies to the repeated differential and proves middle
exactness of the displayed short complex, not short exactness at its endpoints.
It does not yield nontrivial Klein-bottle cohomology. The contraction uses
the real scalar `1/2`; no characteristic-free claim is made for that step.
`ModuleCat` forgets topology, while the preceding maps retain their proved
continuity. The homotopy is not asserted to square to zero.

## Audit of the five proposed consequences

This ledger records scope, not newly formalized theorems. Elementary
counterexamples and literature are separate from the kernel claim.

| Proposed implication | Precise retained statement or missing hypothesis |
|---|---|
| Polarization gives even/odd multiplication | Valid over an associative ring via Peirce projections. In characteristic two, reflection can be the identity while the direct decomposition remains nontrivial. |
| Every odd direction is Grassmann nilpotent | Each directed off-diagonal corner squares to zero; their sum need not. The actual odd mirror has square one. |
| A commutator square is strictly positive | For self-adjoint inputs and the positive Hilbert adjoint, `C* C = -C^2` is nonnegative. Commuting inputs give zero. Positive definiteness or a uniform lower bound needs further conditions; a Krein adjoint alone gives no positive order. |
| Odd squares automatically give physical supersymmetry or geometric curvature | The proved algebraic statement is `d_q^2 = ad(q^2)`. A physical representation or geometric connection is additional data. |
| A boost is intrinsically irreversible | For `B^2=1`, `exp(t B)` still has inverse `exp(-t B)`. Dissipation needs its own dynamical structure. |
| A nilpotent exponential has zero Bregman divergence | `N^2=0` makes `exp(tN)-1-tN=0`. For the squared Frobenius-norm potential, the divergence along a nonzero nilpotent direction is nevertheless positive. |
| Any state gives a faithful modular/GNS geometry | Faithfulness or support reduction, normality, and operator domains must be specified. The pre-GNS form can be degenerate. |
| All finite composition-closed maps are reversible | The existing theorem assumes a finite group; its map specialization uses permutations. Arbitrary self-maps include noninvertible idempotents. |
| Grothendieck completion reverses every flow faithfully | The existing completion is for additive commutative monoids. Its canonical map is injective exactly under cancellation. This is not a generic noncommutative flow theorem. |
| Polynomial covariance implies moment or spectral conservation | Scalar moments need an invariant functional. Covariance does not fix the operator, and moment equality alone need not determine spectrum. |
| Kernel verification removes every classical axiom | The actual dependency audit may include `propext`, `Classical.choice`, and `Quot.sound`; these are permitted foundational axioms. |

The finite-group and cancellation owners are
`Projective.KleinErlangenProgramGroupsAndProjectiveTransfer`
(`klein_fn8_finite_mul_closed_has_one_and_inv`) and `Algebra.Grothendieck`
(`grothendieckMap_injective_iff_cancellation`).

## Analytic and arithmetic evidence

- The original [Madelung paper](https://www.math.toronto.edu/khesin/papers/madelungARMA.pdf)
  uses `sqrt(rho) exp(i theta/2)` and accounts for a `1/4` symplectic
  normalization. The wavefunction target excludes zeros; a global phase lift
  needs the topology hypotheses. This is not an identification with every
  projective quantum state.
- [Michor, section 1.4](https://www.mat.univie.ac.at/~michor/cohom-diffeom-group.pdf)
  states that the smooth diffeomorphism-group exponential is smooth but not
  locally surjective. [Inci--Kappeler--Topalov, Theorems 1.2/B.2](https://arxiv.org/pdf/1107.0488)
  give the precise regularity-loss statement for Sobolev inversion. Failure
  of local invertibility is distinct from failure of smoothness.
- [Araki relative entropy](https://ems.press/content/serial-article-files/41836?nt=1)
  permits `+infinity`. [Hiai, section 5](https://arxiv.org/pdf/1805.02050)
  states relative-modular power-domain conditions.
  [Witten's crossed product](https://doi.org/10.1007/JHEP10(2022)008) permits
  divergent trace integrals; it does not ensure universal entropy finiteness.
- [Witten, equation (3.19)](https://arxiv.org/pdf/1803.04993) gives
  `J Delta^(it) J = Delta^(it)` for antiunitary Tomita conjugation, while
  `J (log Delta) J = -log Delta`. The real linear sheet swap here is not
  silently identified with that antiunitary or a flow-reversing involution.
- [Sutherland's verification records](https://math.mit.edu/~drew/shortgrh/)
  report checks of the five RH/Dirichlet-GRH statements at `lsernau/grh-lean`
  revision `72fead102f663d5c7a407964a13dc0cf9d977207`; its
  [axiom log](https://math.mit.edu/~drew/shortgrh/compact-axioms.log) lists the
  standard three axioms. This task inspected sources and records, without a
  local rebuild of that proof. The repository already has the pinned
  `integrations/grh` lane and real doubled readout adapters. Arbitrary
  Dedekind/automorphic L-functions are outside the five verified statements.
- For positive-definite `G`, LogDet divergence against `diag(G)` equals
  `sum_i log(G_ii) - log(det G)`. The correct native declaration for a future
  specialization is `InfoGeometry.Jordan.steinLoss` in `Jordan/BurgStein.lean`,
  with `Canonical.GaussianBurgStein` supplying positivity and Gaussian KL.
  `InfoGeometry.Jordan.logDetBregman` in `Jordan/LogDet.lean` instead denotes
  a squared log-determinant difference. The external covolume theorem permits
  singular Gram families and quantifies complex field automorphisms; a real
  carrier/determinant-normalization adapter is separate work.
- In the standard completion, a nontrivial zeta zero `rho` gives a pole of
  `Lambda(2s-1)/Lambda(2s)` at `s=rho/2`. RH places these on `Re(s)=1/4`,
  distinct from the unitarity line `Re(s)=1/2`; see
  [Borthwick's scattering formula](https://math.dartmouth.edu/~specgeom/Borthwick_slides.pdf).
  Boundary unitarity and reflection alone do not exclude off-line poles:
  `(s-a)/(s-(1-a))` for real `a != 1/2` is a direct counterexample. Poles
  require meromorphic order/continuation, not totalized pointwise division.

## Validation and acceptance

The existing Klein-section workflow is extended to the new owner and its
additional imports. It compiles exact source with the native pins, requires
zero warnings in selected owners, and audits their private/generated as well
as public declarations. All 33 repository source paths in this import closure
are included in the workflow triggers.

Generation, semantic audit, and final acceptance are separate roles. The PR
records actual commands, hashes, declaration counts, CI results, and any root
gate failures. An interrupted execution is not a successful build. This
contract alone is not evidence that a planned check passed.
