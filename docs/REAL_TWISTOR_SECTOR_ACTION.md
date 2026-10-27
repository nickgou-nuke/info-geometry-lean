# Real twistor operators and a constrained configuration-sector action

## Theorem contract

The requested extension connects the real polynomial operators in PR #227 to
a concrete action, physical constraints, adjoints and normalized states in a
chosen sector. The scope selected here is a stationary configuration-mixing
model. All new carriers, forms and operator algebras are over `ℝ`.

The ambient carrier is the existing `MvPolynomial ι ℝ` representation, with
`create i = M_(X i)`, `annihilate i = pderiv i`, and the constructed positive
factorial `fockPairing`. The actual degree-one coefficient projector selects
the finite one-excitation sector. Number-conserving bilinears
`create i * annihilate j` preserve that sector. Individual creation and
annihilation operators do not preserve it, and finite-dimensional CCR are
not asserted.

The concrete instance uses the existing three-configuration Hamiltonian

```
[ a  0  g ]
[ 0  a  g ]
[ g  g  c ]
```

through an explicitly proved intertwiner with the polynomial operators.
The three coordinates are configuration amplitudes in an externally chosen
common symmetry sector. Auxiliary polynomial degree is not nuclear particle
number, angular momentum, spatial parity, isospin or twistor helicity.

The actual dual carrier remains `V × Module.Dual ℝ V`. Operator dualization
uses `LinearMap.dualMap`. The lift `(v,φ) ↦ (Av,φ ∘ A)` is self-adjoint for
the neutral pairing. It is not claimed to be an algebra homomorphism on
arbitrary noncommuting endomorphisms. A self-adjoint finite configuration
operator commutes with the existing transported fundamental symmetry.

For the real inner-product duality `e`, the positive graph embedding is
`j(v) = (v/2,e(v))`. It satisfies

`neutralForm (j(v)) (j(w)) = inner ℝ v w`.

The positive graph and the configuration/degree projector are distinct
constructions. Unit positive-graph states are not ambitwistor-null states.

The concrete constrained spectral action is

`S(v,λ) = inner ℝ v (H v) / 2 - λ * (inner ℝ v v - 1) / 2`.

Its actual scalar directional derivative, including multiplier variations,
is proved with Mathlib calculus. Vanishing in every direction is proved
equivalent to both `H v = λ • v` and `inner ℝ v v = 1`. This is a
Rayleigh--Ritz stationary action, not an integrated time-dependent action.

The normalized dark and bright states and the calibrated probe reuse the
existing three-configuration graph maps. Their polynomial/dual realization
preserves inner products, the eigen-equations and the operator transition
matrix element. The bright-state equation and the existing strength formula
are used only on their stated real domain `E ≠ c`. Bright-state stationarity
additionally requires the secular equation `(a - E) * (c - E) = 2 * g^2`.

## Source-confirmed owners and dependency order

1. `Twistor/RealTwistorPolynomialCCR`: actual polynomial multiplication,
   derivations, CCR, `linearForm`, `euler`, and monomial occupation identities.
2. `Twistor/RealTwistorFockPairing`: `fockForm`, strict positivity,
   `create_annihilate_adjoint` and `annihilate_create_adjoint`; the map to the
   infinite algebraic dual is only injective.
3. `Twistor/RealDualTwistor`: genuine dual carrier and nondegenerate neutral
   and symplectic forms.
4. `Twistor/RealDualTwistorKreinBridge`: constructed finite-dimensional real
   inner-product duality, `lightconeDoubled`, `hessian_lightconeDoubled`, and
   `neutralForm_fundamental_eq_positive`.
5. `Physics/NuclearThreeConfiguration`: actual real continuous Hamiltonian,
   retained projector, graph reconstruction and proved self-adjointness.
6. `Physics/NuclearThreeConfigurationTransition`: nonzero dark/bright states,
   eigen-equations, two induced metric weights, actual probe and normalized
   transition readout.
7. `Physics/NuclearDoubledConfiguration` and
   `Physics/NuclearRealClockTransitionStrength`: existing paired adjoints and
   two-quadrature normalization; phase rotations and Krein sheet grading
   remain separate.

The source-confirmed gap addressed here is the polynomial sector intertwiner
and its connection to an actual stationary-action derivative and the genuine
dual positive graph. Existing Feshbach, Krein-adjoint and normalization owners
are reused rather than replaced.

## New proof owners

Paths in this table are relative to `lean/InfoGeometry/`.

| Owner | Constructed objects and decisive results |
| --- | --- |
| `Twistor/RealTwistorOneParticleSector` | Degree-one coefficient projector; idempotence, nonzero/nonidentity witnesses, range characterization, Fock self-adjointness; actual `oneBody A = ∑ Aᵢⱼ create i * annihilate j`, transpose-adjointness, faithfulness and projector commutation |
| `Twistor/RealTwistorOneParticleRealization` | Injective Euclidean-to-polynomial map preserving the constructed Fock pairing and intertwining the actual polynomial operator with `A.toEuclideanLin` |
| `Twistor/RealTwistorOneParticleDual` | Coefficient retraction; faithful genuine-dual embedding and retraction; preservation of both evaluation forms, both-leg operator intertwiners and identification of the positive graph with an actual Fock covector |
| `Twistor/RealDualTwistorPositiveSector` | Native algebraic dual lift; normalized positive graph; neutral-self-adjoint positive projector; exact lightcone transport, eigen-equations and transition pairings |
| `Twistor/RealTwistorSpectralAction` | Exact line expansion, actual `HasDerivAt`, and stationarity equivalent to the normalized eigen-equation |
| `Physics/NuclearTwistorConfigurationSector` | The existing three-configuration Hamiltonian and probe realized by the polynomial operators; exact off-diagonal amplitude and preserved number/positive-graph projectors |
| `Physics/NuclearTwistorStationaryStates` | Actual polynomial and genuine-dual actions; graph-constrained variation; constructed normalized dark/bright stationary states |
| `Physics/NuclearTwistorTransition` | Operator-defined strengths on polynomial and dual states; equality with the established nuclear and doubled-clock readouts; complete output-basis norm sum rule |
| `Physics/NuclearTwistorSectorExample` | Three explicit stationary states with nonzero mixing, two exact operator strengths and their model-specific unit sum |

`Physics/NuclearTwistorSectorAudit` collects the decisive axiom-footprint
queries and imports the earlier real-twistor audit. Both repository aggregate
entrypoints import this new audit; `Twistor/RealConstructs` imports the generic
new twistor owners.

## The actual operator and constraint chain

For the polynomial embedding `ι` and coefficient retraction `r`, the code
proves `r ∘ ι = id` and `ι ∘ r = P₁`. The induced maps on genuine duals are

`E(v,φ) = (ι(v), φ ∘ r)` and `R(p,ψ) = (r(p), ψ ∘ ι)`.

They satisfy `R ∘ E = id` and `E ∘ R = dualLift P₁`. Both the symmetric
neutral form and the alternating evaluation form are preserved. Moreover,
`dualLift (oneBody A) ∘ E = E ∘ dualLift A.toEuclideanLin`, including the
contravariant covector leg. Thus the finite dual carrier is an actual
projected subspace of the polynomial/algebraic-dual carrier.

The positive graph is identified explicitly:

`E(j(v)) = (ι(v)/2, fockToDual (ι(v)))`.

This uses no infinite-dimensional Riesz isomorphism. The ambient
`fockToDual` remains injective, with no claim of surjectivity.

The sector constraints have different roles:

| Constraint | Meaning and status |
| --- | --- |
| `P₁ p = p` | Actual one-excitation polynomial subspace; its vectors satisfy `euler p = p` |
| `P₊ z = z` | Actual positive graph in the finite genuine-dual carrier, equivalently `φ = 2 e(v)` |
| `H p = E • p` | Derived from stationarity in all state directions |
| `fockPairing p p = 1` | Derived from the independent multiplier variation; transported to unit neutral norm on the positive graph |
| `E ≠ c` | Real domain of the eliminated-channel inverse; retained for bright eigenstates and the closed strength formula |
| `(a-E)(c-E) = 2g²` | Additional condition for a bright reconstructed vector to be stationary |

The full polynomial creation/annihilation pair has the previously proved
algebraic adjointness. The number-conserving operator obeys
`oneBody A` adjoint to `oneBody A.transpose` under the Fock form. The concrete
Hamiltonian and probe are symmetric matrices, hence Fock-self-adjoint. The
genuine-dual number projector, positive projector and Hamiltonian have their
neutral self-adjointness proved directly. Self-adjoint configuration operators
preserve the positive graph.

For either positive realization, the derivative actually computed is

`dS(v,μ) = B(v, Hx - E x) - μ * (B(x,x) - 1) / 2`.

The generic action theorem's positivity premise is discharged by the
constructed Fock pairing, or by the finite real inner product on the positive
graph. It is not assumed for the whole indefinite dual carrier. Variations of
the dual action stay in that graph through `j(x + t v)`.

## Real reduction domain and normalization of both external states

The reused graph reconstruction is

`Ω(E)(x,y) = (x, y, g(x+y)/(E-c))`.

For `E ≠ c`, this is the concrete eliminated-channel reconstruction belonging
to the earlier Feshbach proof. Its induced norm is

`‖Ω(E)(x,y)‖² = x² + y² + g²(x+y)²/(E-c)²`.

The dark vector `(1,-1)` has weight `2`; the bright vector `(1,1)` has weight
`2 + 4g²/(E-c)²`. Each external vector is divided by the square root of its
own weight. For the concrete real probe `diag(κ,-κ,0)`, the code defines the
matrix element first and then proves its squared value:

`S = κ²(E-c)² / ((E-c)² + 2g²)`.

The dark eigenstate exists directly even when `a = c`. This fact does not
extend the resolvent through its pole. The scalar strength identity is an
algebraic readout for every `E ≠ c`; interpreting its bright vector as a
stationary eigenstate also requires the secular equation above.

## Exact nonzero-mixing example

With `a = 1`, `c = 0`, `g = 1` and `κ = 1`, the Hamiltonian is

```
[ 1  0  1 ]
[ 0  1  1 ]
[ 1  1  0 ]
```

The normalized configurations are the direct evaluations of the constructed
states:

| State | Coordinates | Energy |
| --- | --- | --- |
| Dark | `(1,-1,0) / √2` | `1` |
| Upper bright | `(1,1,1) / √3` | `2` |
| Lower bright | `(1,1,-2) / √6` | `-1` |

All three constructed polynomial states are proved stationary. All three
energies avoid `c = 0`. The operator strengths from the dark state to the
upper/lower bright states are exactly `2/3` and `1/3`, with proved sum `1`
in both polynomial and genuine-dual realizations. This unit sum is specific
to the chosen probe and initial state. The general proved basis sum is the
squared norm of the probe image.

These are normalized probe strengths, not two spontaneous-decay branching
probabilities: the transition to energy `2` is upward. The energies are in a
chosen model unit and are not assigned to measured isotope levels. The proof
constructs the three stationary states; it does not separately formalize a
complete spectral-decomposition theorem.

## Physical interpretation boundary

The model represents configuration mixing inside an externally chosen common
symmetry sector. A particular isotope, its `J,π,T,Tz` assignments, and the
identification of the probe with a physical `E2` or `M1` tensor require separate
representation, selection-rule and experimental input. Neither polynomial
degree nor the sign of the neutral form supplies those quantum numbers.

This package gives a constrained stationary action with positive physical
normalization. It does not claim a real-time evolution law, a Nambu
fundamental identity, a BRST reduction, or nuclear chirality from doubling.
The equality with the existing two-quadrature clock readout is established
for the chosen representatives; clock rotations are not asserted to preserve
the positive graph. Unit graph states are proved not to satisfy the separate
ambitwistor-null condition.

## Verification record

The extension adds 10 Lean modules, including the audit module, with 140
named lemmas/theorems. Its final native proof audit passed with the unchanged
repository pins:

- Lean `4.34.1`, compiler commit
  `5045d0056413266e57c625dcd7c365b10e377c52`;
- Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

The disposable serial checker used the repository shared build lock and
native `lean --root=<source-root> -o <output> <source>` invocations. Source
and dependency hashes matched the final source bytes. The target
`InfoGeometry.Physics.NuclearTwistorSectorAudit` passed with **121 local
source modules** in its actual import closure. That closure uses Lean,
Mathlib and Std externally, without the root Atlas/GIFT/Architect packages.

| Check | Result |
| --- | --- |
| Final affected-source native check | PASS; zero errors and warnings |
| Axiom footprints | 83 queries: 39 earlier twistor queries plus 44 new sector queries; only `propext`, `Classical.choice`, `Quot.sound` |
| Independent fresh native axiom probe | PASS; all 83 queries, zero errors and warnings |
| Repository staged proof-integrity gate | PASS, with the existing gate unchanged |
| Source axiom/debt audit | All 32 Lean files changed by the full PR clean; zero `sorry`, `admit` or explicit axiom gaps |
| Whitespace, staged/source consistency and unchanged dependency pins | PASS |
| Independent semantic review | PASS, including the scalar-action expansion, genuine-dual bridge, external normalization and interpretation of the example |
| Independent final QA | `ACCEPTED_WITH_LIMITED_SCOPE` |

Pre-existing linter warnings seen while first compiling some reused nuclear
dependencies are unchanged. The final new-source check and the independent
fresh native axiom probe are warning-free. No linter or integrity gate was
disabled. The scalar polynomial identity in the action proof is applied only
after actual operator linearity and bilinear symmetry have been evaluated.

The accepted scope is the direct native proof package. The full root Lake
build and repository publication gate remain unverified for the previously
recorded environment reasons: absent/untracked `external_refs/atlas-lean`, an
uninitialized GIFT gitlink, and the broad Architect pin's toolchain
incompatibility. The PR remains a draft. No toolchain, Lake configuration or
dependency pin was changed to hide those requirements.

Once the authentic root dependencies are supplied, the repository-native
target is:

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Physics.NuclearTwistorSectorAudit
```

The complete root publication check remains a separate gate:

```sh
bash scripts/quality/post_build_gate.sh --full
```
