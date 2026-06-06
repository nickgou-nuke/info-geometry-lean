# Fibonacci Colimit, Carrier Cone, and Braided Category Implementation Plan

Date: 2026-06-06

This plan records the repo-grounded path for connecting the existing
inductive/direct-limit algebra, Fibonacci anyon braid lanes, and proper
self-dual carrier cones.  Archive material and external repositories are useful
as references, but Lean source files in this repo remain the proof authority.

## Authority Boundary

- Do not rebuild the categorical infrastructure already mapped in
  `docs/CATEGORICAL_INFRASTRUCTURE_MAP.md`.
- Owner surfaces are the Lean files, especially:
  `lean/InfoGeometry/Algebra/Grothendieck.lean`,
  `lean/InfoGeometry/Canonical/TensorTowerColimit.lean`, and
  `lean/InfoGeometry/Categorical/FibonacciBraiding.lean`.
- Matrix-level Fibonacci calculations are instances or witnesses, not
  replacements for categorical tensor, associator, braiding, pentagon, and
  hexagon infrastructure.
- Graph, Arango, archive, wiki, and external-repo evidence is navigation only.
  Kernel-checked Lean edits decide truth.

## Existing Proven Infrastructure

### Direct-Limit Algebra

The strongest direct-limit algebra owner is
`lean/InfoGeometry/Algebra/DirectLimitSuperClosureLemmas.lean`.

It already provides:

- `bondMap`
- `DirectLimitSuperClosure`
- `directLimitOf`
- `directLimitLift`
- `CompatibleCone`
- `directLimitEndomorphism`
- transport of zero-exactness, injectivity under injective bonds, square-zero,
  nilpotence, idempotence, commuting families, superclosure, and mixed odd-odd
  closure into the direct limit.

Additional tower owners:

- `lean/InfoGeometry/Canonical/SplitCliffordDirectLimit.lean`
- `lean/InfoGeometry/Clifford/Cl11TensorTowerLimit.lean`
- `lean/InfoGeometry/Clifford/CliffordBott.lean`
- `lean/InfoGeometry/Algebra/InductiveSuperClosureLemmas.lean`
- `lean/InfoGeometry/Algebra/InfiniteSuperClosureLemmas.lean`
- `lean/InfoGeometry/Algebra/InfiniteInductiveSUSY.lean`
- `lean/InfoGeometry/Algebra/ErlangenColimitResolution.lean`

Implementation rule: reuse these APIs for all "infinite limit" claims.  Do not
state an infinite theorem as a finite theorem with a name change.

### Fibonacci Colimit And Grothendieck Lane

The relevant checked files are:

- `lean/InfoGeometry/Topological/FibonacciColimit.lean`
- `lean/InfoGeometry/Canonical/FibonacciGrothendieckLimit.lean`
- `lean/InfoGeometry/Canonical/StableFibonacciAnyonBraidLimit.lean`
- `lean/InfoGeometry/Canonical/FibonacciHadjiivanovMonodromyBridge.lean`

Current state:

- `FibonacciColimit.lean` transports finite Fibonacci Artin, inverse, golden,
  square-root, phase, trace, determinant, discriminant, and Casimir readouts to
  an algebraic direct limit.
- `FibonacciGrothendieckLimit.lean` builds an additive direct-limit lane for
  Fibonacci fusion vectors and connects it to charged-Fock and Sugawara
  readouts under explicit hypotheses.
- `StableFibonacciAnyonBraidLimit.lean` is a generic image-local stable braid
  gate compatibility surface, not yet the direct-limit owner.
- `FibonacciHadjiivanovMonodromyBridge.lean` is an honest bridge skeleton.  It
  still lacks a concrete finite Fibonacci braid stage, a parafermion Hilbert
  carrier, and a theorem identifying the colimit carrier with logarithmic
  monodromy.

### Proper Self-Dual Cone Carrier

The relevant checked cone files are:

- `lean/InfoGeometry/Convex/SelfDualCone.lean`
- `lean/InfoGeometry/Projective/SelfDualCone.lean`
- `lean/InfoGeometry/OperatorAlgebra/SelfDualChiralConeBoundary.lean`
- `lean/InfoGeometry/Canonical/StandardFormCore.lean`

Current state:

- `Convex/SelfDualCone.lean` is the clean Hilbert-space owner for
  `SelfDualCone`, `innerDual_eq`, cone rays, interior rays, and paired cones.
- `SelfDualChiralConeBoundary.lean` is a witness-gated boundary socket.  It is
  useful for connecting fixed chiral boundary data, but it is not itself a
  proof that an algebraic direct limit is a proper Hilbert cone.
- `StandardFormCore.lean` supplies vector-state and standard-form carrier seed
  data.  It explicitly stops short of full Tomita-Takesaki standard form.

Implementation rule: the self-dual cone should live on an explicit Hilbert
carrier with inner product and duality data.  The algebraic direct limit can map
into that carrier, but should not be declared self-dual until the topology,
inner product, closure, and dual equality are formalized.

### Braided Category Lane

The proper target is a real `CategoryTheory.BraidedCategory` instance only
after the following are defined and checked:

- actual category
- tensor product
- tensor unit
- left and right unitors
- associator
- pentagon and triangle coherence
- braiding isomorphisms
- hexagon coherence

The existing `Categorical/FibonacciBraiding.lean` owner must be inspected and
extended rather than bypassed.  Matrix equations and phase identities may feed
the finite-stage construction, but they do not by themselves constitute a
`BraidedCategory` instance.

## External Reference Use

Use the external repos only as patterns:

- `external_refs/atlas-lean/Atlas/TensorCategories/code/DualCategory.lean`
  contains useful `MonoidalCategory` and half-braiding design patterns, but also
  scaffolding and `sorry`s, so it is not proof authority.
- `external_refs/Lean-QuantumInfo/QuantumInfo/Finite/CPTPMap/CPTP.lean`
  contains finite tensor, swap, and associator patterns.
- `external_refs/Lean-QuantumInfo/QuantumInfo/Finite/ResourceTheory/FreeState.lean`
  contains finite resource-theory tensor bookkeeping.
- AFP/Isabelle category pages are conceptual references only unless ported
  natively to Lean.

## Implementation Stages

### Stage 0: Preserve Owner Map

Before editing categorical code, re-read:

- `docs/CATEGORICAL_INFRASTRUCTURE_MAP.md`
- `lean/InfoGeometry/Algebra/Grothendieck.lean`
- `lean/InfoGeometry/Canonical/TensorTowerColimit.lean`
- `lean/InfoGeometry/Categorical/FibonacciBraiding.lean`

Output: no code unless an owner gap is found.

### Stage 1: Rehome The Fibonacci K0 Ring

Create a real owner file:

- `lean/InfoGeometry/Algebra/FibonacciGrothendieckRing.lean`

Use:

- `InfoGeometry.Algebra.Grothendieck`
- existing `K0`/Grothendieck universal-property API
- Fibonacci fusion rule `tau * tau = one + tau`

Do not overwrite the untracked scratch file
`lean/InfoGeometry/Algebra/K0FibonacciRing.lean`; treat it as a source of
lemmas to re-express through the real owner API.

Minimum deliverables:

- a two-generator Fibonacci fusion semiring/ring presentation
- a checked `tau_sq_eq_one_add_tau` lemma
- an evaluation hom into a target semiring/ring satisfying the same relation
- a compatibility lemma with `FibonacciGrothendieckLimit.lean`

### Stage 2: Upgrade Stable Fibonacci Braid Limit To Direct-Limit API

Create:

- `lean/InfoGeometry/Categorical/FibonacciBraidDirectLimit.lean`

Use:

- `DirectLimitSuperClosureLemmas.lean`
- `Topological/FibonacciColimit.lean`
- `Canonical/StableFibonacciAnyonBraidLimit.lean`

Minimum deliverables:

- a finite-stage braid gate family indexed by `Nat`
- compatible stage maps
- direct-limit action/lift
- transport lemmas for the Artin/Fibonacci braid relations already proved in
  `FibonacciColimit.lean`

Do not claim braided category coherence here.  This stage is the algebraic
direct-limit action layer.

### Stage 3: Define The Proper Carrier Cone Socket

Create:

- `lean/InfoGeometry/Categorical/FibonacciSelfDualCarrier.lean`

Use:

- `Convex/SelfDualCone.lean`
- `OperatorAlgebra/SelfDualChiralConeBoundary.lean`
- `Canonical/StandardFormCore.lean`

Minimum deliverables:

- a structure for a Hilbert carrier of the Fibonacci direct-limit action
- a field containing a `SelfDualCone`
- positivity and cone-preservation fields for braid/direct-limit actions
- a theorem that direct-limit algebraic observables preserve the carrier cone,
  stated under explicit carrier hypotheses

Do not assert properness unless the owner structure includes pointedness,
closedness, convexity, and nonempty interior or the repo already has the
corresponding definition.

### Stage 4: Attach O(5,5) / Majorana Boundary Modes As A Realization

Use existing topological and boundary files as the carrier realization lane.
Likely candidates include the RealMajorana, bulk-boundary, and Clifford
direct-limit modules discovered by repo search.

Minimum deliverables:

- a named carrier realization structure
- maps from the Fibonacci braid direct-limit action into boundary zero-mode
  endomorphisms
- cone preservation hypotheses or proofs
- a no-vacuum/vacuum-candidate predicate using graph-current presence,
  proof-processing absence, empty protected harmonic intersection, and owner
  equivalence only as a diagnostic predicate, not as a proof of mathematical
  emptiness

### Stage 5: Fill The Hadjiivanov Colimit Gap

Create:

- `lean/InfoGeometry/Canonical/FibonacciHadjiivanovColimit.lean`

Use:

- `FibonacciHadjiivanovMonodromyBridge.lean`
- `FibonacciBraidDirectLimit.lean`
- carrier cone socket from Stage 3

Minimum deliverables:

- finite Hadjiivanov/Fibonacci stage structure
- compatible monodromy maps
- direct-limit monodromy action
- theorem that the carrier action agrees with the direct-limit braid action
  under explicit compatibility hypotheses

### Stage 6: Build The Actual BraidedCategory Instance

Only after Stages 1-5, extend the categorical owner:

- `lean/InfoGeometry/Categorical/FibonacciBraiding.lean`

Minimum deliverables:

- the category of Fibonacci sectors or finite semisimple Fibonacci modules
- tensor product and tensor unit
- associator with F-symbol data
- pentagon proof
- braiding isomorphisms with R-symbol data
- hexagon proof
- final `BraidedCategory` instance

Failure condition: if associator/unitors or pentagon/hexagon are replaced by
`True`, witness packets, opaque certificates, or matrix-only commentary, the
instance is not acceptable.

## First Safe Coding Slice

The first implementation slice should be Stage 1 plus a small Stage 2 readout:

1. Add `Algebra/FibonacciGrothendieckRing.lean`.
2. Prove the native Fibonacci K0/fusion-ring relation.
3. Add only import-safe links to `Canonical/FibonacciGrothendieckLimit.lean`.
4. Add a small direct-limit braid readout if it can reuse existing
   `FibonacciColimit.lean` lemmas without introducing new categorical claims.
5. Run targeted Lean checks on all touched files.

This slice is low-risk because it strengthens an existing algebraic owner lane
without pretending to solve full braided-category coherence.

## Verification Gates

For each stage:

- `lake env lean <new-file>`
- `lake env lean <modified-owner-file>`
- targeted `#check` scratch only when needed, then remove scratch
- no `sorry`, `admit`, fake `True` theorem, or theorem that merely restates a
  field projection unless the theorem is deliberately named as a projection

Before any broad commit:

- run the narrow files first
- then run the smallest relevant `lake build` target
- inspect `git diff` to ensure no archive overwrite or unrelated dirty-file
  changes were included

## Current Conclusion

The plan is viable if implemented in layers:

1. direct-limit algebra and Fibonacci K0/fusion-ring semantics,
2. direct-limit braid action,
3. Hilbert carrier with self-dual cone,
4. boundary/zero-mode realization,
5. Hadjiivanov monodromy bridge,
6. actual `BraidedCategory` coherence.

The immediate implementation target is not the full braided category.  It is
the checked algebraic and carrier infrastructure needed so that the final
braided category instance has real objects, tensor, associator, braiding, and
coherence proofs rather than matrix-level placeholders.
