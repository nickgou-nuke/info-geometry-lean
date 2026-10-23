# Real geometric Bogoliubov integration: contracts and corrections

Companion to [the task plan](REAL_GEOMETRIC_BOGOLIUBOV_IMPLEMENTATION_PLAN.md).
Status: mathematical targets and source-backed API guidance, NOT checked Lean
declarations. Proposed identities must be aligned with current owner conventions
and kernel-checked before promotion.

## 1. Correct the carrier before constructing a waveplate

The existing owner is H = `DoubledSpace E`, with positive product Hilbert
structure and phase operator K(x,y) = (-y,x). The source definitions give
K = J ε, where J is the doubled swap and ε(x,y) = (x,-y).

The earlier proposed construction on E × E using an extra phase J_B on E is
only valid when that additional phase actually exists on E. Substituting the
existing K on H into it silently constructs H × H. Do NOT do this.

Reuse `phaseFlow`/`KRotation` on H. If the physical/geometric waveplate requires
an independent polarization factor, locate its existing carrier and prove its
relation to H; do not add it without resolving the dimensional and action issue.

## 2. Elliptic and hyperbolic laws are different

With I denoting the identity endomorphism, the existing phase flow is

    R(t) = cos(t) I + sin(t) K,     K² = -I.

Its inverse is R(-t). For a square-plus-one generator F the corresponding
hyperbolic formula is

    H(t) = cosh(t) I + sinh(t) F,  F² = I.

`ProjectorEquivariance.chiralBoost` uses F = ε. It must not be silently replaced
by the swap J. Neither F² = I nor invertibility proves positive-Hilbert
orthogonality. In particular, ε-generated boosts scale the ε sectors.

At t = π/4 the phase flow is equal-weight real geometric mixing:

    R(π/4)(x,y) = ((x-y)/√2, (x+y)/√2).

This is NOT the same formula as the determinant-minus-one Hadamard coordinate
change (x,y) ↦ ((x+y)/√2,(x-y)/√2). Prove the reflection/sign factor relating
it to `rotation45`; do not identify the maps by their angle names.

An optical quarter-wave plate at 45° has an axis angle and a retardance.
A spin rotor also uses a half-angle relative to its sandwich action. Record
all three conventions before claiming agreement with `Uqwp`.

## 3. Exact grading transport on the current doubled carrier

From Kε = J and εK = -J, expansion gives

    R(-t) ε R(t) = cos(2t) ε - sin(2t) J,
    R(t) ε R(-t) = cos(2t) ε + sin(2t) J.

At t = π/4 these are respectively -J and J. These signs determine which
sector is called plus. For Γ = -J, the plus sector is {(x,-x)} and the minus
sector is {(x,x)}; for Γ = J the names reverse.

This concrete rotation of real sectors is not, without a comparison map, the
separate circular-eigenvector construction in a complex matrix presentation.
Its projectors are (I ± Γ)/2, obtained by conjugating existing projectors.

Proof strategy: reuse closed forms, inverse laws and projector transport; use
endomorphism extensionality only for the final coordinate readback. Prove the
general parameter identity before specializing if no equivalent result exists.

## 4. Native Mathlib implementation choices

The following APIs were located in the pinned local source. Their full typeclass
requirements must be checked at implementation time; no dependency edits.

| Purpose | Native API / local source |
|---|---|
| Bounded real operators | `ContinuousLinearMap`; existing owner `H →L[ℝ] H` |
| Bounded equivalence conjugation | `ContinuousLinearEquiv.conjContinuousAlgEquiv`, used by the native adjoint implementation |
| Hilbert isometry conjugation | `LinearIsometryEquiv.conjStarAlgEquiv`, `Mathlib/Analysis/InnerProductSpace/Adjoint.lean` |
| Evaluation convention | `conjStarAlgEquiv_apply_apply`: e A e⁻¹ acting on vectors |
| Quadratic generator map | `CliffordAlgebra.map`, `Mathlib/LinearAlgebra/CliffordAlgebra/Basic.lean` |
| Generator readback | `CliffordAlgebra.map_apply_ι` |
| Clifford equivalence | `CliffordAlgebra.equivOfIsometry` |
| Universal representation | `CliffordAlgebra.lift` with the actual quadratic relation proved |
| Real product Hilbert norm | Existing `DoubledSpace`/`WithLp 2` infrastructure; relevant Mathlib `InnerProductSpace/ProdL2.lean` |

For active convention use e = R(t), yielding A' = R(t) A R(-t).
For passive convention use e = R(-t), yielding A' = R(-t) A R(t).
Do not mix the corresponding state-vector conventions.

Use `map_mul`, `map_add`, `map_one`, inverse and star laws of native equivalences
instead of rebuilding these laws in a new packet. A theorem-only bridge can use
local `let` bindings to existing constructions; no global replacement carrier
is needed. If a missing native equivalence adapter is genuinely necessary,
justify it separately and keep it at the lowest suitable existing owner.

Use `simp only` with oriented evaluation/inverse lemmas; `ext` for operator
equalities; `noncomm_ring` for ordered associative algebra identities. Do not
apply commutative `ring` to noncommuting operators. Scalar normalization may use
`ring`/`nlinarith` after the operator expression has been separated.

## 5. Keep mode covariance distinct from representation implementation

Let V be mode space, S the representation space, and γ : V → End(S).
The general CAR relation is

    γ(u)γ(v) + γ(v)γ(u) = 2 b(u,v) I.

For a b-isometry B, mode pushforward γ_B(v) = γ(Bv) satisfies the same CAR.
This follows directly by evaluating the original relation at Bu,Bv.

An implementer U on S requires the additional theorem

    U γ(v) U⁻¹ = γ(Bv).

No implication from mode covariance alone to this identity is allowed.
`RealMajorana.transportGamma` is the former construction. Its transform also
requires parity compatibility. Concrete closure must prove every required law
for the actual representation, not receive them as new assumptions.

The current Majorana API uses one S for mode arguments and endomorphism target.
Do not globally refactor it merely to express V and S separately. First seek an
existing more general owner; if a genuine separate-space lemma is needed, prove
it with native maps and show the existing owner is its concrete instance.

Clifford algebra functoriality gives algebra maps from quadratic isometries.
It does not automatically give boundedness, *-compatibility for every chosen
involution, or spatial implementation on a fixed Hilbert representation.

## 6. Full block and pairing transport

For complementary projectors P+ and P-, retain all blocks Pε A Pδ. Prove

    A = P+ A P+ + P+ A P- + P- A P+ + P- A P-.

Conjugation transports each block and its products. Complementary projectors
do not imply central projectors. The two corners alone need not recover A.

If g(x,y) = <F x,y> with fundamental symmetry F and e is a positive Hilbert
isometry, the transported form in the new state coordinates x' = e x is

    g'(x',y') = g(e⁻¹x',e⁻¹y'),    F' = e F e⁻¹.

Preserving the original g additionally requires e⁻¹ F e = F. For the phase
rotation and an anticommuting F this is not generally true. Do not infer it
from `KRotation_preserves_inner`. Use the actual pairing theorem in the owner.

Distinguish Hilbert adjoint, Krein adjoint, Clifford reversion, grade involution,
and Tomita adjunction. Each comparison needs a proved map and convention.

## 7. Real geometric pairs and Cayley–Dickson comparisons

A square-minus-one B gives a candidate real map (a,b) ↦ a·1+bB from the ordinary
complex algebra. Prove its multiplication and unit laws. Injectivity requires
linear independence of 1,B; do not assume it from notation. For B²=+1 use the
split-complex multiplication instead, again proving independence and readbacks.

For operator coefficients, the source has

    (A+B K)(C+D K) = (AC-BD) + (AD+BC)K

under the specified commutations of K with C and D. The coefficients need not
commute with one another. Do not drop those phase commutations or claim that
(A,B) ↦ A+BK is injective for unrestricted endomorphism coefficients: for any
B, choosing A=-BK gives zero. A genuine pair representation needs specified
complementary coefficient subspaces or another established uniqueness theorem.

Quaternionic comparison additionally requires two square-minus-one generators
with the correct anticommutation and independence. Split-quaternionic signatures
must be stated separately. Cayley–Dickson doubling includes a chosen involution
and multiplication convention, not just a pair of vector spaces.

Associative Clifford algebras cannot contain octonions as faithful multiplicative
subalgebras. Left multiplication operators on octonions are associative under
composition but generally L_a L_b ≠ L_(ab). A comparison through such operators
must retain the associator defect and cannot claim an algebra homomorphism.

Acceptance for each comparison: exact carrier, product, involution, linearity,
injectivity/surjectivity scope, geometric action, and native owner readbacks.

## 8. Soldering contract

For a genuine geometric soldering map e_x : T_x M → V_x, require the actual
bundle carrier, smoothness/regularity, fiberwise invertibility, and stated
quadratic compatibility q_x(e_x v) = g_x(v,v). This induces the corresponding
Clifford map by the universal property.

For tangent/frame transformation F_x and internal transformation B_x, prove

    e'_x F_x = B_x e_x.

For spinor implementer U_x, prove the Clifford-action compatibility

    U_x c_x(e_x v) U_x⁻¹ = c'_x(e'_x(F_x v)).

Each equation must match the actual source/target fibers and representation
convention. If only a vector-space frame map exists, call it that; do not claim
a solder form or global bundle theorem.

Calling B_x Bogoliubov additionally requires preservation of the relevant CAR
quadratic form or CCR symplectic form. An invertible solder map alone does not
supply that property. A boost preserving an indefinite form need not preserve
the positive Majorana CAR form used by `RealMajorana`.

For varying U and convention ψ' = Uψ, D' = U D U⁻¹, a connection D=d+A has
A' = U A U⁻¹ - (dU) U⁻¹. Derive this via the owner's connection API and Leibniz
rule; a constant-frame conjugation theorem omits this derivative obligation.

## 9. GNS and commutant contracts

For an already constructed representation (π,H,Ω) and Hilbert isometry e:

    π'(a) = e π(a) e⁻¹,    Ω' = e Ω.

Prove cyclicity and expectation transport. For an algebra automorphism α,
state pullback and implementation are separate: if ω∘α=ω, the dense GNS rule
U[ a ] = [ α(a) ] is the candidate to prove well-defined and isometric, then
extend with existing completion infrastructure. Do not assume invariance.

The commutant equation must name its ambient operator algebra. If representing
complex-linearity by a real phase K, the corresponding operators commute with K.
The full real commutant can be larger than the commutant within that phase-linear
algebra. Under e, transport K to e K e⁻¹ and prove the centralizer comparison.

Do not identify the concrete doubled J with Tomita J_ω without proving the
dense-domain action, closure, and polar decomposition compatibility. Finite
adjunction and bounded frame rotation do not alone establish analytic KMS.

## 10. Regression and acceptance matrix

| Check | Failure it prevents |
|---|---|
| t=0 gives identity; both inverse orders | Wrong parameter or sign |
| General-angle grading formula before π/4 | Hidden conjugation reversal |
| Readback on each doubled component | Silent extra doubling or wrong carrier |
| Elliptic vs hyperbolic generator squares | Rotation/boost conflation |
| Positive and Krein pairings checked separately | False isometry claim |
| Actual parity commutation | Invalid Majorana-transform instance |
| Concrete CAR realization traced | Field-projection masquerading as construction |
| Mode covariance vs UγU⁻¹ independently checked | False implementability |
| Nonzero off-diagonal product retained | Scalar/diagonal proxy closure |
| Coefficient independence checked | Noninjective pair presentation |
| Multiplication/involution preserved explicitly | False hypercomplex equivalence |
| Real vs phase-linear commutant distinguished | Wrong von Neumann algebra |
| Bundle regularity and overlap laws | Local algebra promoted to global geometry |
| GNS domains and stage maps traced | Formal colimit promoted to analytic closure |

These are proof obligations and audit cases, not substitutes for Lean proofs.
Use concrete nonzero instances for nondegeneracy claims; do not impose needless
nontriviality on identities valid in the zero space. Report precise remaining
debt instead of weakening the target silently.

## 11. Quaternionic null shells: correct carrier-specific contract

This section corrects the premature restriction of the discussion to a 3+1
Minkowski light cone. The inspected repository has the real doubled quaternionic
carrier H = DoubledSpace (Quaternion ℝ). On the split form, the relevant target
is

    Q(p,q) = ‖p‖² - ‖q‖²,
    Q(p,q)=0 iff ‖p‖=‖q‖.

The norm equality follows from nonnegativity and equality of squares, once the
existing coordinate/quadratic readbacks have been aligned with the native norm.
Do not skip that alignment between distinct quaternionic and Quat4 owners.

For r>0, the fixed common-radius shell is

    {(p,q) | ‖p‖=r and ‖q‖=r} = sphere(0,r) × sphere(0,r).

Each quaternionic factor is a real four-dimensional Euclidean sphere, hence an
S3 after scaling. The full shell has two independent S3 factors. A single S3
appears after fixing one factor or imposing a proved relation such as q=p;
the latter is only a particular null subspace slice, not the whole cone.

Candidate nonzero null-cone parameterization to prove using native sphere
subtypes and existing quaternion norm APIs:

    (p,q) ↦ (r, p/r, q/r),   r=‖p‖=‖q‖>0,
    (r,a,b) ↦ (r•a,r•b),     ‖a‖=‖b‖=1.

Use real scalar multiplication by r⁻¹, not quaternion division notation in the
Lean contract. Prove inverse laws, continuity, and the treatment of the excluded
apex separately. At r=0 the shell collapses to (0,0). Quotienting by positive
scaling differs from quotienting by all nonzero real scalars: the latter also
identifies simultaneous antipodes. Do not conflate these quotients.

Neither the equal-norm equation nor the shell parameterization identifies r
with physical time, modular time, boost rapidity, or a rotor angle. Locate the
existing clock/readout owner and prove the particular relation, including units,
sign, and scaling convention. A split (4,4) null cone has no automatically
selected one-dimensional future time coordinate.

Likewise a quadratic function called `Casimir` is not automatically a central
element in an enveloping algebra or its represented operator. The inspected
`OperatorZornCasimirNullIdentity` and `OperatorZornCasimirNullReadout` explicitly
restrict themselves to quadratic algebraic readouts. Reuse actual Poincare or
other symmetry owners only after specifying the group/Lie algebra, represented
generators, centrality/invariance theorem, and map from this geometric shell.

Multiplication warning discovered during source tracing:
`Projective/Cl44QuaternionSplit.lean` explicitly defines a non-standard product
chosen for top-row matrix compatibility. Its `splitOctonion_matrix_homomorphism_topRow`
does not establish a full matrix algebra homomorphism. The doubled carrier and
pairing readbacks remain distinct from any claim about that multiplication.
Prefer the canonical native algebra owner found by D0; do not silently repair
or replace this different product in a theorem-only waveplate bridge.

All assertions of located source scope above are source inspections, not new
kernel checks. The sphere/homeomorphism and clock/Casimir connections are proof
targets pending discovery and verification, not repository-wide absence claims.
