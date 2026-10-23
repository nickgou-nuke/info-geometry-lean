# Real geometric Bogoliubov integration: implementation plan

Status: planning contract, not a formalization or kernel-verification report.
Prepared: 2026-10-22. Source baseline observed on `main`:
`15a7292090c7d9f29206772b5a78ab876e6f0412`, with pre-existing staged changes.

This plan supersedes the construction order proposed in the accompanying chat.
In particular, it does NOT authorize a second doubled carrier, waveplate, CAR
algebra, GNS construction, or assumption-bearing capstone. The immediate target
is a substantive theorem-only composition of existing owners. The broader
abstraction, soldering, and representation tasks below are separate milestones.

See [mathematical contracts and audit gates](REAL_GEOMETRIC_BOGOLIUBOV_CONTRACTS.md)
for conventions, corrected formulas, failure cases, and native API choices.

## 1. Goal and proof boundary

Connect existing doubled-real geometric phase and hyperbolic flows to their
projector, noncommutative operator, Majorana, and representation transports.
Generalize reusable mathematics at the native Mathlib layer, then instantiate
it on the actual Hestenes–Krein owners. Where a geometric soldering form is
involved, prove its precise compatibility rather than naming it Bogoliubov.

The geometric phase axis is a represented square-minus-one action, not an
independent scalar amplitude. Complex/quaternionic coordinates may be compared
through proved real-algebra representations. They must not replace the real
geometric owner or erase noncommutative off-diagonal operations.

Completion requires maps and proofs connecting the layers. A list of separately
proved facts, generic conditional theorem, or field projection is not the
concrete end-to-end closure.

## 2. Source observations and reuse map

These are bounded source observations, not fresh build results or an exhaustive
inventory. Paths below are relative to `lean/InfoGeometry/`.

| Owner | Observed reusable surface | Boundary |
|---|---|---|
| `Krein/DoubledSpace.lean` | `clockAxis`, `complex_i`, `spectral_epsilon`; phase axis acts as `(x,y) ↦ (-y,x)` | Axis already acts on `DoubledSpace E`; do not double it again implicitly |
| `Krein/HilbertBridge.lean` | `rotation45`, isometry/equivalence conversions, `neutralLift` | Real coordinate transport is not automatically the optical matrix waveplate |
| `Canonical/ProjectorEquivariance.lean` | `HestenesI`, `phaseFlow`, `chiralBoost`, projector readbacks | Boost uses `spectral_epsilon`; `coordinate_equivariance` is associativity, not a new covariance construction |
| `Canonical/BogoliubovTransport.lean` | `KRotation`, phase-linear/antilinear operator decomposition, flow machinery | Check every generator and adjoint hypothesis before composing |
| `Canonical/BogoliubovClosedForms.lean` | Existing trigonometric/hyperbolic formulas consumed by projector transport | Reuse instead of reproving exponentials |
| `Canonical/BogoliubovProjectorTransport.lean` | `spectralPlusProj_comp_KRotation`, minus counterpart, boost transport, `majorana_fixed_eq_weylPlus_add_mirror` | Fixed-state premise is explicit; do not identify every state as Majorana-fixed |
| `Quantum/GeometricTensorTransport.lean` | `KRotation_preserves_inner` and operator-metric transport | Positive inner product and Krein pairing are distinct |
| `Quantum/RealMajorana.lean` | `RealBogoliubovTransform`, `transportGamma_car`, Weyl-sector transport | `transportGamma v = gamma (B v)` is mode pushforward, NOT implementer conjugation; datum supplies CAR |
| `Canonical/HestenesPhaseSemilinear.lean` | Commutation/anticommutation with the internal phase axis | No need for a new scalar-complex semilinearity carrier |
| `Canonical/HestenesComplexTranslation.lean` | `hestenesCoeff`, coefficient multiplication, phase-linearity readback | Multiplication formula requires stated phase commutations; unrestricted coefficients are not a unique pair representation |
| `CliffordWeyl/PeirceCircularQwpBridge.lean` | Finite waveplate unitarity and projector comparison | Comparison target only; not the infinite-dimensional representation |
| `Canonical/HestenesCircularCARTransport.lean` | Native Clifford projectors and ladder products | Trace the concrete representation before claiming mode-field covariance |
| `Canonical/FiniteHestenesTomitaBridge.lean` | Finite adjunction and left/right exchange | Not by itself full modular theory |

`Canonical/RealHestenesKreinPipelineCapstone.lean` was inspected: its transport
readbacks depend on supplied frame/calibration fields. It must not be used as
evidence that this concrete waveplate/GNS construction is already completed.

Related plan: [Real Doubled-Krein Bilingual Bridge](REAL_DOUBLE_KREIN_BILINGUAL_BRIDGE_PLAN.md).
Reuse its relevant owner pointers; this plan does not alter its glide scope or
authorize its execution commands. Do not conflate affine base actions with
linear fiber actions.

## 3. Mandatory discovery before Lean edits — task D0

- Read current `AGENTS.md`, canonical pipeline, deep-search protocol, and
  `ASTAQLHASH-HOWTO.md`; inspect their tool implementations before running them.
- Search recursively across repo-owned Lean and relevant tooling using short
  keywords, then exact qualified declarations after discovery. Search imports,
  instances, consumers, alternate carriers, and existing comparison maps.
- Include `eikonal`, `phase`, `rotor`, `boost`, `Majorana`, `solder`, `frame`,
  `vielbein`, `Cayley`, `quaternion`, `octonion`, `CAR`, `GNS`, `commutant`.
- Inspect existing local declaration/edge exports and, when accessible, query
  live AQL read-only. No graph refresh, ingestion, collection writes, or new
  agent tasks are authorized by this planning document.
- Resolve apex names to graph IDs; validate edge direction from exporter source.
  Keep type/value edges distinguished. Record generation, source fingerprints,
  algorithm versions, bounds, pagination, and truncation. Missing metadata means
  freshness unknown, not fresh.
- Trace multi-apex corridors for phase/projector transport, CAR covariance,
  concrete representations, and soldering. Hash matches suggest inspections;
  they do not justify replacements or equivalences.
- Search installed pinned Mathlib separately. Do not update dependencies.

Deliverable: source/declaration table with exact signatures, actual assumptions,
imports, consumers, source hashes, and search coverage. Mark each task below as
reuse, substantive composition, genuine new lemma, false proposed claim, or
not yet resolved. No repository-wide absence claims from a bounded search.

## 4. Causal task graph

```text
D0 owner and native-API discovery
 └─ A0 carrier, phase, adjoint, parity, angle contracts
     ├─ A1 native transport abstractions ─ A2 concrete phase/boost alignment
     │                                    └─ A3 45° grading/projector theorem
     │                                        └─ A4 full operator covariance
     ├─ B0 concrete Majorana-field audit ─ B1 mode CAR covariance
     │                                      └─ B2 representation implementation
     ├─ C0 existing geometric bundles/frames ─ C1 soldering compatibility
     └─ D1 coordinate algebra/involution audit ─ D2 representation comparisons

A4 + B2 + applicable C1/D2 ─ E0 existing GNS/state transport
                            └─ E1 commutant/Krein/modular transport
                                └─ E2 compatible colimit passage
```

This is an obligation graph, not a statement that all nodes are missing or
that every branch is needed for the first theorem-only bridge.

### Source-first amendment: quaternionic null shells

Do not start this branch by imposing a conventional 3+1 spacetime carrier.
The following owners were inspected after the user's null-shell clarification:

- `Projective/QuaternionicDoubledKrein.lean` defines
  `QuaternionicKreinCarrier := DoubledSpace (Quaternion ℝ)` and proves
  `splitOctonion_splitKreinForm_readback` plus coordinate round trips.
- `Projective/QuaternionicKreinForm.lean` defines the difference of the two
  quaternionic real inner products and proves an indefinite-sign example.
- `Superalgebra/CayleyDicksonMajoranaG2Lightcone.lean` proves
  `cayley_dickson_diagonalizes_interval` and `lightcone_iff_equal_quat_norms`
  on its separate explicit `Quat4` coordinate carrier. Do not identify this
  carrier/product with the native quaternionic owners without comparison maps.
- `Canonical/SplitOctonionBogoliubovCarrierBridge.lean` provides actual
  `splitOctonionQuaternionicCarrierEquiv` and `quaternionCoordinateEquiv`, as
  well as transported hyperbolic generators. Its concrete one-doubling lane
  must be distinguished from its generic datum-based and twice-doubled lanes.
- `Krein/SplitOctonionDoubleKreinSheetBridge.lean` connects concrete creation/
  annihilation operators with split-octonion sheet coordinates. Its documented
  scope is coordinate/action compatibility, not equality of products.
- `Physics/SplitOctonionPoincareCasimirBridge.lean` proves a Pauli determinant
  readback for a symmetric fixed section. `PoincareCasimirCentralityBridge`
  uses a supplied Poincare-generator relation structure. Neither observation
  identifies the entire quaternionic null cone with a represented Casimir shell.

New dependency branch, after D0/A0 and in coordination with the main thread:

1. Align the native quaternionic carrier, coordinate norm, and split quadratic
   form by existing maps and explicit norm-preservation proofs.
2. Prove the null-locus equal-norm characterization on that actual carrier.
3. Identify fixed positive common-radius shells with the product of two native
   quaternionic metric spheres; prove both maps and their inverse laws.
4. If a single S3 is intended, specify which quaternion/direction is fixed or
   which additional relation is imposed, and prove that slice/fiber theorem.
5. Identify the common radius with a time interval only through a specified
   clock/flow/readout map and proved normalization. Do not define this identity
   solely to make a desired theorem tautological.
6. Connect the resulting quadratic constraint to an actual represented Casimir
   through the existing representation and invariance/centrality owners.
7. Prove which transformations preserve the null cone, which preserve each
   shell, and which change radius. These are different stabilizer statements.

For the direct split quaternionic form, the expected nonzero null-cone
parameterization is positive radius times S3 times S3. This is a mathematical
target inferred from the norm equation, NOT a located or kernel-checked
homeomorphism. See the companion contracts for qualifications.

Search provenance: recursive lexical scans covered `lean/` and `proofs/`,
followed by selected owner/import/consumer inspection. Some broad outputs were
truncated, so this is not exhaustive semantic coverage. Local DAG metadata
reports a 2026-10-10 export rooted at `InfoGeometry.Physics.All`; do not treat
it as current whole-repository coverage. A read-only live query against
`infogeometry` returned module groups and zero writes; a later metadata/apex
query was denied by the environment. No refresh was performed and live
generation freshness was not established. Continue D0 before novelty claims.

## 5. Tasks and acceptance criteria

### A0 — Freeze the actual mathematical objects

Record the actual real carrier, positive inner product, Krein form, fundamental
symmetry, phase axis, grading, parity, and source/target representation spaces.
Separate mode space from spinor/GNS space even if an existing API identifies
their underlying types. Identify actual eikonal definitions and domain/codomain
maps; a name or physical interpretation is insufficient.

Use distinct notation for the doubled swap, geometric phase, chirality,
fermion parity, and Tomita conjugation. Prove identifications only when valid.

Acceptance: all subsequent equations type-check on these objects; no silent
doubling, scalar extension, signature change, or multiplication-side change.

### A1 — Native abstraction layer

Use `LinearMap`, `ContinuousLinearMap`, `LinearEquiv`, `ContinuousLinearEquiv`,
`LinearIsometryEquiv`, `AlgHom`, `AlgEquiv`, and `StarAlgEquiv` as appropriate.
Use existing quadratic forms, submodules, and Clifford universal properties.

Do not introduce a structure carrying the desired rotation/CAR/KMS conclusions.
Generic theorems may have honest necessary hypotheses, but concrete closure
requires proving those hypotheses for the selected existing objects.

Prefer the native conjugation equivalence over manually restating every ring
law. New lemmas should express substantive compatibility with the geometric
owners, not renamed copies of `map_mul` or existing results.

Acceptance: exact local API signatures and coercion directions recorded; narrow
imports; no dependency modifications or competing replacement APIs.

### A2 — Identify phase flow and distinguish boost flow

Prove any needed equality between `phaseFlow` and `KRotation` from existing
closed forms and the `HestenesI`/`clockAxis` definitions. Reuse group/inverse laws.
Identify `chiralBoost` with the corresponding existing epsilon-generated boost,
not an arbitrary J-generated boost.

Specialize the existing family at the agreed angle; do not define a second
waveplate function merely to give the specialization a name.

Acceptance: both inverse directions, exact parameter/sign conventions, positive
inner-product preservation reused for the elliptic flow, and accurate separate
pairing behavior for the hyperbolic flow.

### A3 — The 45° geometric grading/projector theorem

Compose existing projector transport with the phase closed form. Prove the
conjugated grading and identify its projectors with existing sector owners.
Use the corrected formulas in the contracts file to audit signs.

Do not claim agreement with the finite optical waveplate until the represented
generator and conjugation direction are matched. An equal mixing coefficient
does not establish that comparison.

Acceptance: projector idempotency/complementarity reused, exact range/kernel
identifications, sector transport in both directions, concrete angle readout.

### A4 — Simultaneous state/operator covariance

Apply native conjugation to the same isometry used on states. Prove the action
intertwining and bilinear expectation identity on all vectors. Preserve full
operator multiplication, adjoints, and all four chiral blocks.

Use a concrete existing noncommutative pair to demonstrate that off-diagonal
operations have not been removed. Do not infer that the chiral projectors are
central or that their corner algebras exhaust the original algebra separately.

Acceptance: operator/state square commutes; blocks reconstruct every operator;
sector-changing products survive; self-adjointness and spectral comparisons
use the appropriate native real/complex operator-algebra formulation.

### B0 — Audit the actual Majorana representation

Locate concrete constructions of the Majorana field and their CAR proofs.
`RealMajoranaDatum.car` is a supplied field: `transportGamma_car` is reusable
covariance, but does not construct that datum or prove its premises anew.
Find the actual instance and trace its Clifford action, boundedness, linearity,
adjoint law, parity, and scalar normalization.

Acceptance: cite the actual constructed representation and proof of its CAR,
not merely the generic structure or a theorem projecting its `car` field.

### B1 — Reuse mode-space CAR covariance

Instantiate the existing transform with the concrete phase flow and proved
inverse/isometry/parity laws, if an appropriate instance already exists.
Do not bypass `parity_even`: prove it for the actual parity or record failure.
Compose `transportGamma_car` rather than rebuilding a CAR carrier.

Acceptance: concrete mode covariance with all instance obligations discharged.
An honest generic result is classified separately from concrete closure.

### B2 — Prove the implementer relation, only where justified

For mode transform B and spinor/representation implementer U, prove
`U γ(v) U⁻¹ = γ(B v)` with the actual action conventions. Do not use B itself
as U without a theorem identifying the two roles. Prove action on generators,
then extend through the existing algebra and representation machinery.

An algebra automorphism, equivalent transported representation, and implementer
inside one fixed representation are different deliverables. Infinite-dimensional
implementation can require additional conditions; prove them or delimit scope.

Acceptance: actual implementer constructed and equivariance proved, or a precise
conditional/obstruction result without claiming full implementation.

### C0/C1 — Soldering and frame compatibility

Locate the actual manifold/bundle or algebraic frame owners. A geometric
soldering form must have its declared domain, target bundle, regularity, and
fiberwise nondegeneracy. An algebraic frame intertwiner is not automatically a
tangent-bundle soldering form.

Use native bundle, differential, and linear-isometry machinery already employed
by those owners. Prove the Clifford compatibility square between the frame
isometry, fiber algebra action, and spinor implementer. If expressing soldering
as a Bogoliubov transform, prove the relevant quadratic/CAR or symplectic/CCR
preservation, rather than treating the terms as synonyms.

For varying frames, use the owner's connection and transformation convention;
include the derivative term in connection transport. Constant-frame algebra
does not prove a global gauge/connection theorem.

Acceptance: typed fiberwise equivalences, regularity and metric compatibility,
action equivariance, and actual overlap/descent laws where a global claim is made.

### D1/D2 — Complex and hypercomplex coordinate comparisons

Keep the native real geometric owner. Search existing complex, split-complex,
quaternion, split-quaternion, and Cayley–Dickson comparison owners independently.
For each proposed representation record multiplication, conjugation/reversion,
unit, norm/quadratic form, associativity, and scalar action conventions.

Prove the actual algebra equivalence or weaker faithful linear/action map.
Do not infer an algebra isomorphism from equal real dimensions or a square-minus-
one element. Prove injectivity and surjectivity separately where claimed.

Octonions are nonassociative: a faithful multiplication-preserving embedding into
an associative Clifford algebra cannot be the promised comparison. Use the
appropriate nonassociative product representation or left/right actions and
state exactly what those maps preserve.

Acceptance: each coordinate comparison has a truthful categorical type and
explicit round-trip/action lemmas; no global slogan identifying all doublings.

### E0/E1 — GNS, commutants, and modular transport

Reuse the existing positive normalized state and GNS owners. Preserve the real
geometric language through the existing internal-phase representation, while
making any complex Hilbert comparison explicit.

First prove transported-representation and cyclic-vector compatibility. Then
separately prove state invariance if claiming implementation in the original
GNS representation. Transport the algebra and commutant in the specified ambient
operator algebra; real and phase-linear commutants need not coincide.

For Tomita/modular claims, identify the cyclic separating vector, dense core,
antilinearity relative to the internal phase, closure, and polar decomposition.
Transport domains before asserting conjugation identities for unbounded objects.
Never identify the doubled swap with modular conjugation from its name alone.

Acceptance: exact state and representation maps, topology/closure results where
needed, and no promotion of algebraic KMS identities to analytic-strip theorems.

### E2 — Existing categorical colimit passage

Read the categorical infrastructure map before this task. Prove compatibility
with connecting morphisms for the actual stage maps, states, and actions. Use
existing colimit universal properties; prove readbacks on stage images.
Use existing completion/GNS infrastructure for the completed representation.
An algebraic colimit does not alone prove boundedness, Hilbert completion,
spatial implementation, or analytic KMS conditions.

Acceptance: all naturality and state-compatibility obligations discharged;
continuum statements match the actual constructed categorical object.

## 6. Verification and integration

For each milestone: record exact proposition, concrete objects, dependencies,
source hashes, proof scope, and exclusions before writing Lean. Recheck current
owners before patching because the main thread may already be implementing the
theorem-only bridge.

1. Reuse or extend the canonical owner; add a focused theorem-only bridge only
   if it composes genuinely distinct owners without an import cycle.
2. Preserve all existing unrelated/staged work. No new branch, no dependency
   updates, no cache deletion, no graph writes.
3. Inspect compiler processes; run verification sequentially under the shared
   build lock using the current repository wrapper and exact affected targets.
4. Check all new propositions for hidden conclusion-as-hypothesis, empty or zero
   carriers, erased off-diagonal structure, fake scalar substitutes, and wrong
   multiplication/adjoint conventions.
5. Run the applicable kernel, axiom, placeholder, semantic-vacuity, owner,
   consumer, and subsystem gates. Broader closure claims require broader checks.
6. Track task-owned changes promptly without staging unrelated concurrent work.
   Commit/push requires the main thread's explicit authorization and coordination.

Deliver a final manifest of exact changed declarations and validation results.
Label each milestone implemented/checked, conditional, obstructed, or deferred.
Do not mark E0–E2 complete because A0–B1 pass.

## 7. Planning-session record

Only this plan and its companion contracts file are authored by this task.
No Lean changes, builds, graph queries, graph writes, agent dispatch, or proof
closure are claimed. Read-only source inspection found native APIs and owner
contracts; exhaustive discovery D0 remains an implementation prerequisite.
