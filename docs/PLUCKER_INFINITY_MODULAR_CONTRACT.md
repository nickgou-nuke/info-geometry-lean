# Plücker, infinity twistor, and modular conjugation

## Intent and source conventions

This addition formalizes the algebraic content of the 27 October 2026 request
to connect six Plücker coordinates, Minkowski intervals, the infinity twistor,
inversion, and logarithmic modular dynamics. The input also proposed that
antisymmetry alone implies the Plücker equation, that an infinity twistor is a
Möbius group element, and that imaginary-time KMS periodicity is an operator
identity. Those statements require correction; they are not proof hypotheses.

Base revision: `b143075bbf27e75860a1011e04423a0f227b7c41`.

Primary mathematical references:

- Tim Adamo, *Lectures on twistor theory*, arXiv:1712.02196v2,
  §§1.1, 1.4, 2.1, 2.3, particularly (2.25)–(2.29):
  <https://arxiv.org/html/1712.02196v2>.
- Edward Witten, *Notes On Some Entanglement Properties Of Quantum Field
  Theory*, arXiv:1803.04993v6, (3.19), (4.26), (4.32), (4.44)–(4.47):
  <https://arxiv.org/pdf/1803.04993>.

## Existing owners and exact reuse boundary

`Projective/KleinQuadricPlucker.lean` owns `Vec4 R`, `Plucker6 R`,
`pluckerLine`, `kleinQ`, `kleinPolar`, and their polarization and scaling laws.
The six coordinates are ordered `01,02,03,12,13,23`, and

```text
kleinQ P = p01*p23 - p02*p13 + p03*p12
kleinPolar P P = 2*kleinQ P.
```

`Twistor/TwoTwistorPlucker.lean` owns the map from the native
`Twistor4 = Spinor2 × Spinor2` to these coordinates. Its
`twistorPairPlucker_on_klein` already proves decomposability implies the
quadric equation. No duplicate Plücker relation is needed.

`Twistor/PenroseIncidence.lean` owns the actual incidence map and submodule:

```text
incidenceLinearMap X π = (i • X.mulVec π, π)
incidencePlane X = LinearMap.range (incidenceLinearMap X)
det_zero_iff_exists_nonzero_kernel X :
  X.det = 0 ↔ ∃ π, π ≠ 0 ∧ X.mulVec π = 0.
```

The factor `i` is part of this owner convention. The graph chart
`π ↦ (Xπ,π)` must be related by an explicit invertible linear map; removing
`i` silently would give the wrong sign in the polar interval.

`Canonical/MatrixTwoNoncommutativity.lean` owns the actual opposite matrix
units over an arbitrary nontrivial commutative ring and proves their products
differ. The new block-inversion module proves that the graph chart and block
exchange retain that product-order distinction. No algebra-homomorphism
property is attributed to the Plücker coordinate map.

`Canonical/PauliHestenesSpinMomentum.lean` owns the Hermitian Pauli
paravector and its determinant `t²-x²-y²-z²`. Its matrix is an explicit
finite realization, not a replacement for a von Neumann algebra or a
continuum soldering theorem.

`Canonical/RealTomitaCore.lean` owns the real doubled continuous-operator
carrier, `RealModularLogData`, `flow`, `adjointFlow`, and
`commutantAction A = J*A*J`. The log interface supplies
`exp deltaLog = Delta`; positivity and Tomita standard form do not follow
from that field alone.

`Canonical/BogoliubovTransport.lean` owns the phase axis and generator
`deltaLog.comp clockAxis`. These are arbitrary bounded operators on the
existing real doubled Hilbert carrier, not scalar surrogates.

## Ground-truth theorem contract

### 1. Affine Plücker chart

Carrier: `Matrix (Fin 2) (Fin 2) R` and the existing `Plucker6 R` over a
commutative ring, specialized to a field only when division is needed.

```text
P(X) = pluckerLine (X00,X10,1,0) (X01,X11,0,1)
     = (det X, -X01, X00, -X11, X10, 1).
Q(P(X)) = 0
B(P(X),P(Y)) = det(X-Y).
```

On `p23 ≠ 0`, construct the inverse chart and prove reconstruction from
`Q(P)=0`. Prove the independent nonzero-rescaling invariance of
`B(P,Q)/(p23*q23)`. The chart is not a construction of the complete
Grassmannian quotient or a compactification homeomorphism.

### 2. Infinity twistor and incidence

Carrier: the existing `Twistor4`, its native linear dual, and an alternating
form. The flat infinity form evaluates to
`π₀ρ₁-π₁ρ₀`; its value on a twistor pair is the `p23` coordinate of the
existing Plücker map. Prove its radical is exactly the upper-spinor plane.
Translations preserve it. Determinant-one changes of the lower spinor frame
preserve it; arbitrary frame changes scale it by their determinant.

The form also has an exact geometric relationship to the distinguished
infinity point `infinityPlucker = (1,0,0,0,0,0)`:

```text
kleinPolar P infinityPlucker = P.p23
infinityTwistor Z W =
  kleinPolar (twistorPairPlucker Z W) infinityPlucker.
```

Thus the equation `p23 = 0` is precisely the polar hyperplane of that
infinity point. Its intersection with the Klein quadric specifies the
algebraic infinity section. This identifies the infinity form as a polar
dual; it does not identify the form with the block-exchange transformation.
The owner theorem is
`PluckerInfinityGeometry.infinityTwistor_eq_kleinPolar_infinity`.

Use the actual incidence submodules for the null-intersection equivalence.
Do not define intersection to mean the determinant equation.

### 3. Real form and metric

Six independently real Plücker coordinates give the split form `(3,3)`.
Use a specified conjugation-fixed real slice of the complex Klein carrier
for Lorentzian conformal geometry. Prove its quadratic polynomial explicitly
and connect its affine restriction to the existing Pauli determinant.
The infinity form chooses a chart and scale; it does not change a real
quadratic form's signature.

### 4. Inversion

The actual block exchange `(ω,π) ↦ (π,ω)` induces

```text
S₂(P) = (p23,-p02,-p12,-p03,-p13,p01).
S₂(P(X)) = det(X) • P(X⁻¹), when det(X) ≠ 0.
```

Prove its naturality on decomposable bivectors, involutivity, polar-form
preservation, and origin/infinity exchange. This linear involution and the
degenerate alternating infinity form are distinct typed objects. No assertion
that this bare block exchange lies in `SU(2,2)` is made.

### 5. Native exterior Clifford algebra

Use `ExteriorKleinNullTwistor.exteriorKleinQuadraticForm` on the repository's
literal `ExteriorSquare`, together with Mathlib's `CliffordAlgebra`. Prove
that its canonical generator is a nonunit exactly when the Klein quadratic
value vanishes. On the null cone its square is zero; away from the cone
its inverse is the generator of the vector scaled by the inverse quadratic
value. The projective Klein predicate uses the existing exterior owner.

Nonvacuity witnesses are explicit: the wedge of the first two coordinate
vectors gives a nonzero square-zero, noninvertible generator; the existing
nondecomposable exterior vector of quadratic value one gives a nonzero
self-inverse generator. These are statements in the Clifford algebra of
the six-dimensional exterior carrier. No identification with `Cl(2,2)` is
asserted, and null generators are not inverted to obtain the block exchange.

### 6. Real operator modular conjugation

On the existing arbitrary real doubled bounded-operator carrier, use the
explicit log-reversal hypothesis `J*deltaLog = -deltaLog*J` and the owner's
proved phase-axis anticommutation. Derive commutation with the product
generator, then with its exponential and adjoint flow. The two sign changes
give the same real flow parameter under `J`.

For the separately defined shell conventions
`foc(τ)=adjointFlow(-τ,A)` and
`defoc(τ)=adjointFlow(τ,commutantAction A)`, derive
`commutantAction(foc(τ))=defoc(-τ)`.
This is an operator identity under stated hypotheses; neither a scalar
oscillator model nor a construction of physical wavefront sets. The chosen
bounded exponential flow is not identified with the spectral modular flow
of a faithful state without additional standard-form and logarithm data.

### 7. Continuation: infinity, source/sink sectors, and chiral charge

Intake: the user identifies the infinity twistor with a relationship to the
repository's sources/sinks and the five-grading of chiral parity charges.
The precise continuation is a compatibility of existing constructions, not
an equality of objects with different types. The following contract was
fixed before source promotion and is implemented by the four continuation
owners listed below.

The native owner `Canonical/Cl55InfinityWittBoundary.lean` defines
`infinityClifford55 = ι55 ((1/2) • n_bar_vec)` and
`originClifford55 = ι55 ((1/2) • n_vec)`. Its proved
`infinity_origin_CAR_clifford` is `e*f + f*e = 1`, and both generators
square to zero. Its four left/right grading identities imply
`[infinityGrading55,e] = 2 • e` and
`[infinityGrading55,f] = (-2) • f`.

An explicit coordinate injection sends the existing `ConformalSix` to
`PACSplit55` and then through the existing `pacSplit55ToV55`:

```text
positive coordinates = (a0,0,0,0,bz)
negative coordinates = (ax,ay,az,0,b0).
```

Its six-coordinate left inverse proves injectivity; native `ι55_injective`
also makes the induced vector-to-Clifford map injective. The proved exact
compatibilities are

```text
Q55(embed X) = quadratic24 X
kleinPolar (lorentzPlucker X) (lorentzPlucker Y)
  = -ofReal (polar Q55 (embed X) (embed Y))
e * ι55(embed X) + ι55(embed X) * e = algebraMap (b0+bz).
```

For an actual Penrose pair with the explicit compatibility hypothesis
`twistorPairPlucker Z W = lorentzPlucker X`, the last scalar is precisely
`infinityTwistor Z W`, which is then real. This proves equality of the
actual boundary zero conditions without dropping an imaginary component.
Degenerate pairs are allowed; a nonzero projective point requires its own
nonzero hypothesis. The representative signs are fixed:
`embed(lorentzReadback infinityPlucker) = -infinityVector55`, whereas the
origin maps to `originVector55`.

The existing `Clifford/Cl55CARSpinAutomorphism.lean` defines the same native
generators as `creation55 4` and `annihilation55 4`.
`Clifford/Cl55OperatorFiveGradeClosure.lean` proves their number-adjoint
degrees are respectively `+1` and `-1`; products of two creations have
degree `+2`, and products of two annihilations have degree `-2`. The number
operator `numberOperator55` is the raw sum of five occupations. The matrix
owner's centered `numberOperator` has a different normalization.

The concrete charge in `Clifford/Cl55ChiralGrandCanonical.lean` is
`chiralCharge55 = mixedGenerator55 0 0 - mixedGenerator55 1 1`.
The native mixed-generator commutator identities make mode 4 neutral under
this charge. Pairing it with mode 0 or 1 yields number-degree `+2` source
operators of chiral charges `+1` or `-1`; the corresponding annihilation
pairs have degree `-2` and opposite chiral charges. The actual Clifford
nonzero witnesses require the second mode to differ from 4; repeated-mode
products are separately proved zero. With `e = infinityClifford55`,
`f = originClifford55`, `c_i = creation55 i`, and
`a_i = annihilation55 i`, the exact adjoint eigenvalues are:

| Native operator | Number degree | Chiral charge |
| --- | ---: | ---: |
| `e` | +1 | 0 |
| `f` | -1 | 0 |
| `e*c_0` | +2 | +1 |
| `e*c_1` | +2 | -1 |
| `f*a_0` | -2 | -1 |
| `f*a_1` | -2 | +1 |

The Clifford grade involution negates each endpoint and fixes each quadratic
pair. This even/odd parity is a further distinct quantity, proved using the
native `CliffordAlgebra.involute` operation.

These are three distinct readouts: integer number degree, the local
infinity grading, and the selected two-mode chiral charge. In particular,
the local infinity involution has no nonzero odd Peirce sectors. The full
associative Clifford algebra is not restricted to five degrees: the
existing `Cl55CreationWordGradeObstruction` supplies a nonzero degree-five
word. A five-grade closure concerns the selected linear/quadratic Lie
carrier. No physical current-divergence equation, KMS limit, or new
continuum/colimit theorem is inferred here.

The existing `globalSheetReflectionAlg` is an actual Clifford algebra
equivalence induced by `(p,q) ↦ (p,-q)`. Its creation/annihilation exchange
proves `N ↦ 5-N`, fixed-`N` grade reversal, and source/sink exchange.
The reversal is an equality of actual submodule images for every integer
degree, `F(gradeSubmodule N k) = gradeSubmodule N (-k)`. It also sends the
selected chiral charge and local infinity grading to their negatives.
This native symmetry is not identified with the Plücker block exchange
without a separate action-compatibility theorem.

Discovery used broad owner/dependent searches and the maintained context
preflight. This checkout has no generated declaration-DAG/index artifacts
or available external-reference sources; no claim of graph freshness or
exhaustive external equivalence is made. Current source types, their
dependencies, and the serial kernel check decide the accepted scope.

## Module map

| Module suffix | Responsibility |
| --- | --- |
| `Twistor.PluckerInfinityChart` | Actual minors, affine chart reconstruction, normalized interval |
| `Twistor.InfinityTwistor` | Alternating form, native dual-valued operator, radical, translations |
| `Twistor.PluckerPenroseIncidence` | Explicit factor-`i` adapter and actual incidence-submodule intersection |
| `Twistor.PluckerLorentzRealForm` | Specified conjugation, real six-coordinate injection, Pauli interval |
| `Twistor.PluckerBlockInversion` | Actual block exchange and matrix inverse chart |
| `Twistor.PluckerInfinityGeometry` | Polar dual of the infinity point, arbitrary spinor-frame cancellation, and Minkowski null-intersection theorem |
| `Projective.ExteriorKleinCliffordInversion` | Native exterior Clifford units, null obstruction, explicit witnesses |
| `Canonical.RealModularConjugationBridge` | Bounded operator conjugation, exponentials, oriented shells |
| `Twistor.PluckerCl55InfinityBridge` | Injective Lorentz-six embedding, native Clifford infinity readout, and real-frame boundary equivalence |
| `Canonical.Cl55InfinitySourceSinkGrading` | Native CAR endpoints, nonzero degree-two source/sink words, Clifford parity, and separate local grading |
| `Canonical.Cl55InfinityChiralCharge` | Actual two-mode chiral-charge commutators of the endpoints and quadratic words |
| `Canonical.Cl55InfinityGradeReversal` | Existing global reflection, fixed-number submodule reversal, endpoint and source/sink exchange |
| `Twistor.PluckerInfinityModular` | Aggregate import of the geometric and operator results |
| `Twistor.PluckerInfinityModularAudit` | Transitive axiom check for every declaration owned by the new modules |

All module names have the prefix `InfoGeometry.`. Existing foundational
owners and dependency pins are unchanged.

There are **twelve substantive owner modules**: seven under `Twistor`, one
under `Projective`, and four under `Canonical`. The aggregate contains only
imports. The audit selects those twelve owners by Lean's imported-module
metadata rather than declaration-name prefixes. It checks every owned
constant present in the imported environment, including private and
compiler-generated declarations, rejects introduced axioms and unsafe or
partial declarations, and checks all transitive axiom dependencies. Each
substantive owner must be nonempty; the aggregate must own zero declarations.

## Result classification

The labels below follow `skills/epistemic-compilation/SKILL.md` and refer to
the successful kernel and axiom checks in the diagnostic configuration
recorded below. They do not certify the unchanged pinned build.

| Package | Classification | Exact boundary |
| --- | --- | --- |
| Plücker, infinity, incidence, Lorentz real form, block inversion, and native exterior Clifford results | `[accepted_limited_scope]` | Algebraic chart, quadratic-form, submodule, and Clifford-algebra theorems; no compactification homeomorphism, differential metric tensor, global stabilizer classification, or continuum theorem |
| Native `Cl55` infinity, source/sink grades, chiral charge, and global reflection | `[accepted_limited_scope]` | Explicit coordinate injection and operator identities; the Penrose readout uses the stated real-frame hypothesis, and integer number degree, local grade, charge, and Clifford parity remain distinct |
| Real bounded-operator modular conjugation | `[bucket_2_conditional]` | Uses the existing exponential certificate and the named oddness hypothesis `J*deltaLog = -deltaLog*J`; does not supply a positive spectral logarithm, faithful state, or standard-form commutant theorem |

The focused/defocused shell identity is conditional operator algebra with
explicitly chosen shell orientations. The selected bounded exponential flow
has not thereby been identified with spectral `Delta^(it)`. No
unqualified repository-build success is asserted. The `[kernel_verified]`
result is explicitly diagnostic: Lean `4.34.1`, pinned Mathlib, and the
separately recorded compatible LeanArchitect revision.

## Explicit remaining boundaries

- The stabilizer classification as the Poincaré group requires a specified
  real conformal group, action, and global group theorem.
- There is no state-independent equality between the rank-two skew infinity
  twistor and a positive modular operator. A state and representation must be
  supplied before a comparison theorem can even be typed.
- In finite standard form the modular operator is `Lρ Rρ⁻¹`, not `ρ` itself.
  The repository already has a separate finite standard-form owner.
- KMS is an analytic correlation boundary relation with exchanged operator
  order. No imaginary-time operator periodicity or asymptotic convergence to
  chiral ideals is inferred from taking a logarithm.
- Clifford nullness gives a square-zero generator, not arbitrary zero
  products. The new bridge specializes native Mathlib inversion to the
  literal exterior Klein form and its existing projective predicate.
- No unbounded Tomita theorem, new completion, or categorical colimit is
  claimed from the bounded/finite statements in this addition.

## Validation

### Configurations and current status

| Component | Unchanged repository configuration | Explicit diagnostic configuration |
| --- | --- | --- |
| Lean | `v4.34.1` | `v4.34.1` |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` | Same pinned revision |
| LeanArchitect | `54d3fb249685db8e5a564e0b3f331cff77991607` | `468e8f58fb4ad6e6ad672a08da6d0d0531e95a97` |
| Verification status | **BLOCKED** by the pinned dependency's Lean API incompatibility | **PASS**: all twelve owners and the transitive axiom audit |

The strict check first rejected a previously available LeanArchitect checkout
whose actual revision was `468e8f58fb4ad6e6ad672a08da6d0d0531e95a97`, rather
than the manifest's `54d3fb249685db8e5a564e0b3f331cff77991607`. An isolated,
unmodified checkout of the manifest revision then failed to compile
`Architect/Command.lean` against Lean `4.34.1`: its `exportEntriesFnEx?`
callback has an older return shape than the required `OLeanEntries` result.
This establishes a dependency compatibility blocker; it is not a failing
proof of a newly added mathematical theorem.

The diagnostic run uses the separately identified, unmodified `468e...`
checkout to continue checking the new mathematical sources. The repository's
`lake-manifest.json`, `lakefile.lean`, and `lean-toolchain`, and dependency
sources remain unchanged. No formal equivalence between the two
LeanArchitect revisions is asserted. A dependency pin update remains a
separate approval decision under the repository's dependency policy.

### Reproduction

With the pinned compiler on `PATH` and dependencies checked out at the
manifest revisions, the default strict command is:

```bash
python3 tools/infra/check_plucker_infinity_modular.py
```

Its default target is
`InfoGeometry.Twistor.PluckerInfinityModularAudit`. It checks the focused
source import closure and always reruns the audit. Use `--lean`, `--mathlib`,
and `--lean-architect` to supply existing checkout locations when they differ
from the defaults. The strict command is expected to reproduce the blocker
above until dependency compatibility is resolved.

To reproduce the explicitly separated diagnostic check, replace the example
paths below with existing, unmodified checkouts at the stated revisions:

```bash
python3 tools/infra/check_plucker_infinity_modular.py \
  --lean /path/to/lean-4.34.1-linux/bin/lean \
  --mathlib /path/to/mathlib-at-d13f23b7 \
  --lean-architect /path/to/LeanArchitect-at-468e8f58 \
  --diagnostic-architect-revision 468e8f58fb4ad6e6ad672a08da6d0d0531e95a97 \
  --output .lake/plucker-infinity-modular-diagnostic
```

Both modes run serially under the repository's shared build lock. The checker
validates compiler and dependency revisions, refuses tracked dependency
source modifications or missing owned import sources, and records the
selected source-closure digests. A successful explicit diagnostic run writes
`status: diagnostic_pass` and `pinned_environment_verified: false`, together
with both declared dependency pins and checked revisions. It cannot certify
the unchanged pinned environment. A failed invocation writes a failure
report rather than retaining a previous successful status.

### Completed evidence

| Evidence | Current record |
| --- | --- |
| Diagnostic source-closure compilation | PASS |
| Exact-owner transitive axiom audit | PASS; all twelve substantive owners, aggregate owns zero declarations |
| Audited declaration count | 315, including generated/private declarations |
| Audited theorem count | 273 `.thmInfo` declarations, including generated helpers; not a count of hand-written results |
| Source modules in checked closure | 284 |
| Observed transitive axiom union | Exactly `propext`, `Classical.choice`, and `Quot.sound` |
| Proof-proxy gate | PASS on all fourteen staged Lean files, including the actual matrix-order witness |
| Semantic-vacuity gate | PASS, with 23 reviewed warnings and zero errors: 22 `trivial_surface`, one `dynamic_literal_definition` |
| Placeholder/custom-axiom source scan | No `sorry`, `admit`, or axiom declarations in the fourteen Lean files |
| Independent semantic review | PASS for all twelve owners' stated algebraic and conditional operator scope; all semantic warnings reviewed against actual definitions |
| Whitespace check | `git diff --cached --check` passed |
| Root-package path preflight | BLOCKED: `Atlas` source/config unavailable; `GIFT` gitlink uninitialized in this checkout |
| Root-package build | Not certified by this focused check |

The original fourteen semantic warnings concern four definitional accessors,
two alternation laws, five convention/invariance readouts, two concrete
coordinate evaluations, and the normalized-interval corollary. The eight new
short-proof warnings concern two null-vector reflection formulas, two CAR
pair exchanges, two repeated-mode zero formulas, and two Clifford parity
formulas. These are appropriate helper results. The remaining lexical
warning mistakes zero padding in `conformalSixToPAC55` for a zero-valued
definition: all six input coordinates are retained and injectivity is
proved by a left inverse. None supports a stronger geometric or analytic
claim. No gate was disabled or weakened. The matrix-order witness uses an
existing owner on the same matrix carrier rather than introducing a
surrogate witness assumption.

The machine-readable receipt is
[`PLUCKER_INFINITY_MODULAR_VALIDATION.json`](PLUCKER_INFINITY_MODULAR_VALIDATION.json).
It records the exact checked dependency revisions, source-closure digests,
new Lean source hashes, audit counts, gate results, and existing blockers.
The pinned-build blocker remains explicit despite the diagnostic success.
