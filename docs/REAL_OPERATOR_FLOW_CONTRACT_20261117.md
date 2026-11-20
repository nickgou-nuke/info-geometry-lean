# Real operator exponential bounds: theorem contract

## Provenance and carrier

The two attachments are frozen in `REAL_OPERATOR_FLOW_INTAKE_20261117.md`.
This development starts independently from main
`08c34e03f610b452e03422037949196dc7d92d6d`; it does not modify the previously
published chiral Green PR #373. The proof carrier is an arbitrary complete
normed associative real algebra `A`, with its native multiplication, scalar
action, norm, `NormedSpace.exp`, and the existing `expTransport`. The algebra
and observables need not commute. There is no finite-dimensionality
assumption or external complex scalar in the new theorem statements.

The convention is

`expTransport H X t = exp(t • H) * X * exp(t • (-H))`.

Consequently `[H,X] = λ • X` means growth by `exp(λ*t)` with this order.
Changing conjugation order would reverse that sign.

## Existing owners and the new implication

| Existing source | Inspected content | Intended reuse |
| --- | --- | --- |
| `Physics/HestenesKreinOperatorCalculus` | Real negative/positive-square exponentials; anticommuting mixed square and three exponential regimes | Actual operator exponentials and discriminant, not scalar replacements |
| `Lie/SplitOctonionRegularMultiplicationHestenesBridge` | Generic time-scaled positive/negative scalar-square and square-zero exponentials | Derive global bounds, periodicity, and unboundedness |
| `Canonical/TransportLieDerivative` | Derivative of actual exponential conjugation | Integrate an adjoint eigenoperator's exact flow |
| `OperatorAlgebra/ConservedOperatorFlow` | Group, inverse, multiplication, scalar compatibility; conservation iff commutation | Reuse transport and the stationary direction of the orbit criterion |
| `OperatorAlgebra/TripotentExponentialFlow` | Covariance of actual Peirce projectors; grade preservation iff commuting | Keep spectral components in the actual algebra |
| `Core/TripotentEigenspaces` | Five-grade eigenspaces and a nonzero nonzero-grade witness when the commutator is nonzero | Exclude all growing components from a bounded two-sided orbit |
| `Physics/Algebra/TripotentTopologicalFiveGrading` | Native continuous-linear grade projectors and topological decomposition | Transfer orbit boundedness to genuine operator components |
| `Canonical/GibbsHessianScalarGaugeBridge` | Hessian kernel equals scalar gauge; strict positivity under identifiability modulo scalars | Correct the intake without duplicating this API |
| `Physics/ParaKahlerFisherCompatibilityObstruction` | Anti-isometry and nonnegative Fisher compatibility obstruction | Separate neutral geometry from convex information geometry |
| `Core/TripotentKreinBlocks`, `Core/TripotentStarGrading` | Krein corner map `(a,b) → (swap b,swap a)`; skew-adjoint star preserves grade | Correct the proposed reversion corner exchange |

The bounded search also inspected the named Hestenes loxodromic rotor,
topological rotor, algebraic optical mode, and complex scalar gauge owners.
Their names do not supply the norm-orbit conclusions below. Search findings
are bounded current-source findings, not claims of exhaustive absence from
all repository history or open PRs.

## Selected theorem targets

1. **Adjoint eigenoperator transport.** For `H*X-X*H=λ•X`, prove
   `expTransport H X t = Real.exp (λ*t) • X`, its exact norm, the contraction
   direction for nonzero `X`, and two-sided boundedness iff `λ=0 ∨ X=0`.
2. **Quadratic generators.** For `G^2=q•1`, classify global norm boundedness
   of the actual exponential. With the stated nontriviality hypothesis the
   target is boundedness iff `q<0 ∨ G=0`. A negative square gives an explicit
   period and norm bound; a nonzero square-zero generator gives unbounded
   operator growth. Keep the zero-generator exception explicit.
3. **Tripotent orbit rigidity.** For `S*S*S=S`, prove
   `(∃ C, ∀ t:ℝ, ‖expTransport S X t‖ ≤ C) ↔ Commute S X`.
   This is a statement about the full operator orbit, not just one component
   or a diagonal scalar model.
4. **Commuting rotary extension.** For `S*S*S=S`, `J^2=-1`, `Commute S J`, and `γ≠0`,
   target boundedness of the orbit of `X` under `γ•S+ω•J` iff `Commute S X`.
   Derive the uniformly bounded rotary factor from its real exponential;
   do not assume boundedness of the desired loxodromic orbit. `X` need not
   commute with `J`. Central scalar shifts should cancel from conjugation.

Native acceptance of these statements is recorded in
`REAL_OPERATOR_FLOW_VERIFICATION_20261117.md`, which distinguishes the checked
source closure from root Lake integration and publication-gate status.

## Claim ledger and corrections

| Intake claim | Disposition and corrected scope |
| --- | --- |
| The anticommuting boost/skew mixture squares to `(γ²-Δ²)•1` | Owner-backed under the explicit square and anticommutation hypotheses |
| Scalar Weyl rescaling removes opposite conjugation exponents | False; central factors cancel from conjugation |
| Uniformly bounded finite-dimensional flows must be periodic | False in general: independent rotation blocks with irrational frequency ratio give a bounded nonperiodic group. A single negative scalar-square generator has the stronger common-frequency property used here |
| Every trajectory diverges at a nonzero nilpotent boundary | Overstrong: vectors in the kernel are fixed. The selected result concerns the operator norm of the exponential; `G=0` is stationary |
| Elliptic flow must expand and contract the observer norm | Overstrong: orthogonal rotation has constant norm. Periodicity and norm boundedness do not establish a physical breathing observable |
| The displayed `D=diag(-1,1)/2` gives `M=-2γD-Δ(P₊+K₋)` | Sign error: the displayed matrix is `2γD-Δ(P₊+K₋)`. Also `Δ(K₋-P₊)` is symmetric off-diagonal with the intake's generators |
| Real Cayley conjugation converts a hyperbolic generator into an elliptic one | False: similarity preserves the scalar-square relation and determinant. Bounded projective coordinates do not imply bounded linear operator norm |
| Projectivization violates `π(u+v)=πu+πv` | The displayed projective addition is undefined. Linear lifts and their quotient coordinates must be distinguished |
| A faithful state always has a bounded modular logarithm | Only with further spectral hypotheses; finite-dimensional strict positivity suffices. Infinite-dimensional faithfulness alone supplies no uniform spectral lower bound |
| Entanglement is necessary for a real symmetric density logarithm | False: a strictly positive real symmetric density matrix already suffices, without an entanglement hypothesis |
| Linearly independent, nonscalar statistics make the BKM Hessian positive definite | Insufficient: their span may contain the identity. The existing owner requires identifiability modulo scalar multiples of the identity |
| Neutral para-Kähler signature determines stable/unstable dynamics | Missing a vector field and metric/gradient convention. Signature alone is not a dynamical stability theorem |
| A positive-definite Hessian is necessary for every restoring minimum | Overstrong: a degenerate minimum such as `x⁴` is a counterexample. Nondegeneracy must be stated for a Hessian-based classification |
| Norm-isometric automorphisms are automatically periodic modular rotations | False; isometry does not imply periodicity or identify a modular flow for a specified state |
| Reversion swapping `p` and `q` exchanges `pAq` and `qAp` | False for an anti-automorphism: `τ(p x q)=p τ(x) q`. Existing Krein/star-grade owners already encode the correct corner law |
| Contractive half-line restrictions force Hardy spaces or irreversible dynamics | Not established. Restricting an invertible group to a half-line does not construct a Hardy completion or irreversible physical law |
| A hand-labelled rank diagram proves a unique physical synthesis | Interpretation only; proof dependencies below come from actual theorem use |

## Causal dependency order

Real algebra and existing exponential calculus → exact adjoint eigenoperator
flow → norm and directional bounds → native bounded Peirce projections →
tripotent bounded-orbit criterion. Separately, scalar-square exponentials →
elliptic uniform bounds and parabolic/hyperbolic obstructions. Combining
the tripotent criterion with a commuting uniformly bounded rotary factor
gives the loxodromic orbit criterion.

## Explicit boundaries and verification

No new Spin(1,3) representation, Hardy space, rigged completion, Tomita
operator, KMS state, causal-diamond local algebra, BKM metric, entanglement
construction, superconducting scattering model, or uniqueness theorem for a
physical synthesis is claimed. Existing objects are reused only at their
actual theorem types. The new proofs retain real noncommutative products and
do not create custom axioms or fields assuming their conclusions.

The root agent owns the serialized shared-lock native build and axiom audit.
Candidate generation, semantic review, source gates, and kernel acceptance
are distinct stages. Root Lake integration remains a separate gate from
focused native source-closure verification, with dependency pins unchanged.
