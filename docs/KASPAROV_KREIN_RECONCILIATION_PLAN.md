# Kasparov–Krein Reconciliation Plan

Status: planning document

Scope: reconcile the repository's generalized real Krein/Kasparov interfaces with
their concrete doubled-space, matrix, Clifford, DAG, and finite-dimensional
representations.

This document is an integration plan, not a theorem certificate.  A statement
becomes accepted mathematics only when its owner file type-checks and its
scope is stated honestly.

## 1. Ground truth from the current tree

The repository has two principal owner layers.

### 1.1 Krein carrier and operator layer

The owner is:

- `lean/InfoGeometry/Krein/KreinSpace.lean`
- `lean/InfoGeometry/Krein/DoubledSpace.lean`

`KreinSpace` is a real Hilbert carrier equipped with a fundamental symmetry
`J : H ≃ₗᵢ[ℝ] H`, together with involutivity and Hilbert self-adjointness.
The owner derives `jCLM`, `kreinInner`, `kreinAdjoint`, Krein self/skew
adjointness, and the projector layer.

`DoubledSpace E := WithLp 2 (E × E)` is the canonical concrete carrier.  It
provides `modular_j`, `spectral_epsilon`, `complex_i`, `clockAxis`, and the
`doubledCarrier` package.

There are two distinct symmetry packages here.  The `KreinSpace` instance used
by the doubled Hilbert carrier has its own fundamental symmetry (the sheet sign
flip), while `DoubledSpace.doubledCarrier` is an
`InvolutiveSelfDualCarrier` with `J := modular_j` (sheet swap) and
`ε := spectral_epsilon`.  They are not definitionally the same object.  Every
transport theorem must name which symmetry it uses and prove compatibility;
`doubledCarrier` must not be silently treated as a `KreinSpace` instance.

Theorems to reuse rather than duplicate include:

- `KreinSpace.jCLM_comp_self`
- `KreinSpace.jCLM_adjoint_eq`
- `KreinSpace.kreinInner_kreinAdjoint`
- `KreinSpace.kreinAdjoint_comp`
- `KreinSpace.kreinAdjoint_involutive`
- `DoubledSpace.modular_j_to_doubled`
- `DoubledSpace.doubledCarrier`

### 1.2 Bounded Kasparov-style layer

The primitive owner is:

- `lean/InfoGeometry/KK/RealSplitKreinKasparovCycle.lean`

It packages coefficient rings `A` and `B`, a real Krein-graded Hilbert carrier
`H`, a split `Cl(1,1)` action, even left/right algebra representations, an odd
bounded phase `F`, Krein-skew-adjointness, and compact defect/commutator
conditions.

`lean/InfoGeometry/KK/KasparovCycle.lean` is a compatibility surface:

```lean
abbrev KasparovCycle := RealSplitKreinKasparovCycle
```

It also owns finite-dimensional index readouts and transport lemmas.  It should
not be made into a second independent cycle structure.

The current source explicitly qualifies this as a primitive bounded
real-split-Krein carrier, not a complete standard Kasparov `B`-module.

The adjacent canonical index path is:

```text
KK/DiracFredholmModule.lean
  → KK/DiracFredholmIndex.lean
  → KK/KasparovCycle.lean
```

These files must remain in the owner graph rather than being bypassed by a new
index wrapper.

## 2. Mathlib boundary

Use Mathlib as the implementation substrate, not as a parallel owner:

- `InnerProductSpace ℝ H`, `CompleteSpace H`, and normed/module structures for
  carriers;
- `ContinuousLinearMap` for bounded operators;
- `LinearIsometryEquiv` for the fundamental symmetry;
- `ContinuousLinearMap.adjoint` for Hilbert adjoints;
- `IsCompactOperator` for compactness;
- `Submodule`, `Module.finrank`, and finite-dimensional linear algebra for the
  index layer;
- `StarRing`, `AlgHom`, Lie and graded algebra structures where already used.

The repository's `KreinSpace` class is the owner of the extra indefinite-metric
structure.  Do not introduce a second `KreinSpace` class merely to imitate a
Mathlib name.  Likewise, do not claim that Mathlib supplies a standard
Kasparov-cycle or KK-product implementation unless an actual imported Mathlib
declaration is found and checked.

The concrete doubled carrier also needs the existing
`Krein/HilbertBridge.lean` and `Krein/Clifford.lean` infrastructure.  The
grading instance is not automatically interchangeable between plain
`DoubledSpace E` and the lifted `HilbertDoubled E` carrier.  That conversion
requires an explicit proved equivalence.

## 3. Canonical dependency graph

The target dependency order is:

```text
Mathlib Hilbert/operator primitives
        ↓
KreinSpace
        ↓
DoubledSpace / doubledCarrier
        ↓
KreinGradedModule + RealSplitCl11Action
        ↓
RealSplitKreinKasparovCycle
        ↓
resolvent → bounded transform → compact defects → finite index
        ↓
finite Clifford, equivariant, optical, DAG, and physics instances
```

The categorical and colimit infrastructure remains above the finite carrier
layer.  A limit or colimit statement must use its existing owner modules and
explicit stage maps; it must not be inferred from a finite matrix instance.

## 4. Reconciliation rules

### Rule A — one owner per concept

| Concept | Owner | Concrete realizations |
|---|---|---|
| Fundamental Krein symmetry | `KreinSpace` | diagonal/doubled matrices, finite carriers |
| Doubled real carrier | `DoubledSpace` | `DoubledSpace ℝ`, `DoubledSpace E`, finite matrix models |
| Krein adjoint | `KreinSpace.kreinAdjoint` | finite matrix/Krein adjoint bridges |
| Grading and oddness | `KreinGradedModule` | chiral matrix and Dirac instances |
| Bounded cycle | `RealSplitKreinKasparovCycle` | resolvent and Clifford constructions |
| Legacy KK naming | `KasparovCycle` | compatibility consumers only |
| Finite analytical index | `RealSplitKreinKasparovCycle` / `KasparovCycle` | finite-dimensional carriers |
| Group/Lie equivariance | `RealSplitKreinEquivarianceBridge` | G2, SO4, finite actions |

New modules must import the owner and prove an instance theorem.  They must not
redeclare the carrier, adjoint, grading, or cycle structures.

Phase 0 must classify independent or legacy `KreinSpace`-like structures found
in physics, projective, experimental, generated, and external namespaces.  A
filename containing “Krein” is not evidence that the declaration is a canonical
owner.

### Rule B — every carrier change needs a map

For each concrete representation, provide an explicit map or equivalence:

```lean
E_concrete ≃ₗ[ℝ] E_canonical
```

or, for bounded operators,

```lean
EndConcrete ≃ₐ[ℝ] EndCanonical
```

Then prove the transported operations, at minimum:

1. map preserves addition and scalar multiplication;
2. map preserves composition or multiplication;
3. map preserves the fundamental symmetry;
4. map preserves the Krein pairing/adjoint;
5. map preserves grading and oddness;
6. map preserves compact defect predicates;
7. map preserves the finite index when finite-dimensional.

No theorem may be called an “isomorphism”, “soldering form”, or “equivalence”
unless the corresponding inverse or universal property is present and proved.

For cycle transport, a carrier isometry alone is insufficient.  The transport
packet must also specify compatibility for both Krein symmetries, grading,
`RealSplitCl11Action`, representations `π` and `ρ`, conjugation of `F`, compact
defects, and the finite index.  No `transportCycle` declaration currently
exists; it must not appear in a theorem contract as if already implemented.

### Rule C — finite data stay finite

Finite matrix or Clifford results may instantiate the abstract carrier and cycle,
but do not establish an infinite-dimensional, analytic, equivariant, colimit,
or standard `KK` theorem by themselves.

### Rule D — no vacuous bridges

Reject definitions whose primary action is an identity map, a proposition field
that simply assumes the target theorem, or a theorem that is only `rfl` for a
placeholder construction.  Such code may be retained as explicitly labelled
compatibility scaffolding, but it cannot be promoted as a substantive
Kasparov/Krein theorem.

## 5. Concrete integration phases

### Phase 0 — inventory and quarantine

1. Build a declaration inventory for the owner modules above.
2. Classify files into `owner`, `instance`, `transport`, `compatibility`,
   `experimental`, and `external/auto`.
3. Mark duplicate structures and identity-based placeholders for review.
4. Do not delete or rewrite them in this phase.

Acceptance artifact: a source-linked table of declarations, imports, consumers,
and scope labels.

### Phase 1 — canonical carrier API

Stabilize the small reusable API in `KreinSpace` and `DoubledSpace`:

1. prove the involution and adjoint laws once;
2. expose canonical projector and grading lemmas;
3. reconcile plain `DoubledSpace` with the `HilbertDoubled` carrier used by the
   grading instance through an explicit continuous-linear equivalence;
4. provide explicit finite-dimensional instances only for named finite carriers
   under exact hypotheses such as `[FiniteDimensional ℝ E]`;
5. ensure every matrix representation is connected by a proved linear or
   continuous-linear equivalence.

No Kasparov terminology is needed in this phase.

### Phase 2 — canonical bounded cycle API

Keep `RealSplitKreinKasparovCycle` as the single bounded-cycle structure.

1. Separate primitive fields from derived lemmas.
2. Derive compact commutator and super-commutator consequences from the owner
   fields.
3. Keep `ρ` explicitly documented as an even algebra representation until a
   genuine right-module structure is implemented.
4. Preserve `KasparovCycle` only as a compatibility abbreviation.
5. Add honest predicates for the missing standard Kasparov module laws rather
   than silently assuming them.

Target theorem contracts are schematic until their types are declared:

```lean
theorem transported_cycle_fields
    (eH : H₁ ≃ₗᵢ[ℝ] H₂)
    (hJ : ...)
    (hgrade : ...)
    (hcl11 : ...)
    (hπ : ...)
    (hρ : ...)
    (hF : ...) :
    IsTransportedCycle eH X₁ X₂
```

```lean
theorem finite_index_transport
    (eH : H₁ ≃ₗ[ℝ] H₂)
    (hgrade : ...)
    (hF : ...) :
    finiteAnalyticalIndex X₁ = finiteAnalyticalIndex X₂
```

The ellipses are planning placeholders only. Before implementation, replace
them with exact typed hypotheses and an owner definition for
`IsTransportedCycle`.

### Phase 3 — resolvent and bounded-transform integration

Use the existing sequence:

```text
RealSplitKreinUnboundedCycle
  → RealSplitKreinResolventData
  → RealSplitKreinBoundedTransform
  → RealSplitKreinKasparovCycle
```

The missing analytic functional calculus remains an explicit open boundary.
Do not rename the resolvent into a canonical phase unless its phase laws are
proved.  Every remaining field must be labelled as an assumption-backed datum.

### Phase 4 — concrete finite representations

Integrate concrete owners through constructors and transport theorems:

- `Canonical/RealCl55KasparovCycleBridge.lean` for finite `Cl(5,5)`/CAR data;
- `Canonical/RealCl55SO4EquivariantKasparovCycleBridge.lean` for finite
  equivariance;
- `Physics/KreinDiracKasparovSpinorBilinear.lean` for algebraic eta/gamma
  adjoint identities;
- matrix and Clifford bridge files only when they expose a proved equivalence
  to `DoubledSpace` or the canonical cycle carrier.

Required result for each instance:

```lean
def concreteCycle : RealSplitKreinKasparovCycle A B H
```

followed by nontrivial proofs of its fields and a finite index theorem where
appropriate.

### Phase 5 — DAG and graph integration

`DAG/TwoComplexKasparov.lean` must not be treated as complete until its current
identity-valued `toKasparovCycle` is replaced by an actual construction.

The replacement should proceed in small steps:

1. define the finite chain/cell carrier;
2. define its Dirac operator from the boundary maps;
3. prove grading anticommutation;
4. construct a bounded phase or finite Fredholm datum;
5. prove the cycle fields against the canonical owner;
6. only then define the DAG-to-cycle map;
7. prove functoriality and colimit compatibility separately.

The theorem `toKasparovCycle_is_id` should either be removed, renamed as a
placeholder compatibility fact, or replaced by a substantive theorem.

### Phase 6 — products and equivariance

Do not promote matrix multiplication or tensoring to a Kasparov product.

First formalize a clearly scoped finite composition operation, then prove:

1. well-definedness on the declared carrier;
2. preservation of grading and adjoint laws;
3. compact defect compatibility;
4. associativity;
5. identity element;
6. only afterwards, a theorem connecting it to a standard Kasparov product if
   the required module and analytic structures exist.

## 6. File ownership proposal

| Responsibility | File owner |
|---|---|
| Abstract Krein space | `InfoGeometry/Krein/KreinSpace.lean` |
| Canonical doubled carrier | `InfoGeometry/Krein/DoubledSpace.lean` |
| Grading/Clifford carrier laws | existing `KreinGradedModule` and `RealSplitCl11Action` owners |
| Primitive bounded cycle | `InfoGeometry/KK/RealSplitKreinKasparovCycle.lean` |
| Index compatibility | `InfoGeometry/KK/KasparovCycle.lean`, `DiracFredholmIndex.lean` |
| Resolvent/bounded transform | existing `InfoGeometry/KK/RealSplitKrein*` files |
| Finite Clifford instance | `Canonical/RealCl55KasparovCycleBridge.lean` |
| Equivariance | `KK/RealSplitKreinEquivarianceBridge.lean` and concrete group owners |
| DAG instance | `DAG/TwoComplexKasparov.lean` after nontrivial construction |
| Public facade | `Canonical/KK.lean`, `Canonical/Krein.lean` |

New bridge files should be created only when the map or transport theorem does
not belong in one of these owners.  A bridge file must name the two carriers,
the map, and the compatibility theorem it proves.

## 7. Required theorem contracts before implementation

Each new theorem task must record:

1. exact source owner and imports;
2. exact carrier and operator types;
3. assumptions versus conclusions;
4. map/equivalence used for transport;
5. finite versus analytic scope;
6. adjacent claims explicitly excluded;
7. expected kernel-check command.

Example contract:

```text
Claim: a concrete finite operator datum instantiates
       RealSplitKreinKasparovCycle.
Carrier: Matrix (Fin n) (Fin n) ℝ or a specified finite Hilbert carrier.
Assumptions: proved Krein symmetry, grading, compactness, and representation laws.
Conclusion: an inhabited RealSplitKreinKasparovCycle.
Excluded: standard KKO class, unbounded functional calculus, group integration.
Verification: lake env lean <owner-file>.
```

## 8. Verification and release gates

For every implementation slice:

1. search the existing owner declarations first;
2. write the theorem contract;
3. run a narrow `lake env lean` check;
4. run the semantic-vacuity and placeholder scans;
5. inspect `#print axioms` for new theorem surfaces;
6. run the locked module build sequentially;
7. stage changed files immediately with `git add -A`;
8. report exact files, declarations, build output, and remaining scope debt.

Never use `lake clean`, concurrent builds, generated wrappers, `sorry`, `admit`,
custom axioms, or identity-valued placeholders as proof of a substantive map.

## 9. Definition of successful unification

The reconciliation is complete only when:

- every public Kasparov/Krein theorem has one canonical owner;
- every concrete representation has an explicit proved transport map;
- `KasparovCycle` is only compatibility naming, not a competing structure;
- finite and analytic scopes are separated in declarations and documentation;
- the DAG construction is nontrivial and no longer identity-valued;
- products are not called Kasparov products without their defining laws;
- all touched modules pass the locked build with no new placeholders or custom
  axioms;
- the final report distinguishes kernel-verified theorems from assumption-backed
  structures and open analytic debt.

Until these conditions hold, the repository should describe the system as a
canonical real split-Krein Fredholm/Kasparov-style infrastructure, not as a
fully formalized standard KK-theory implementation.

## 10. Adversarial review corrections

The following constraints supersede any illustrative shorthand earlier in this
document.

### 10.1 Symmetry and grading alignment

The doubled carrier has a real symmetry distinction that must be preserved:

- the `KreinSpace` instance uses the doubled sheet sign flip as its fundamental
  symmetry;
- `DoubledSpace.doubledCarrier` uses `modular_j` as `J` and
  `spectral_epsilon` as `ε` in an `InvolutiveSelfDualCarrier`.

The plan must not identify these packages by name alone.  The missing
`DoubledSpace`/`HilbertDoubled` compatibility map belongs in
`Krein/HilbertBridge.lean` and `Krein/Clifford.lean`, with proved laws for
composition, grading, `Cl(1,1)`, pairing, adjoint, and compactness transport.

### 10.2 Exact transport contract

The illustrative `transportCycle` expression above is not an existing
declaration and is not a sufficient theorem type.  The implementation must
first define a transported-cycle structure or constructor whose data include:

1. the carrier equivalence and both inverse laws;
2. compatibility of the selected Krein symmetries;
3. grading and `RealSplitCl11Action` intertwining;
4. conjugation laws for `π`, `ρ`, and `F`;
5. preservation of oddness, Krein-skew-adjointness, and compact defects;
6. finite-dimensional index preservation under the grading/phase hypotheses.

Only after those fields exist may a theorem state equality or equivalence of
cycles.  Replace all planning ellipses with exact typed hypotheses before
implementation.

### 10.3 Finite Clifford owner split

There are two similarly named finite files:

- `lean/InfoGeometry/Canonical/RealCl55KasparovCycleBridge.lean`;
- `lean/InfoGeometry/KK/RealCl55KasparovCycleBridge.lean`.

They package different matrix-level finite data.  Neither currently constructs
`RealSplitKreinKasparovCycle A B H`.  Phase 4 must choose one finite datum owner,
document the other as a compatibility consumer, and add the missing coefficient
representations, Krein carrier, grading, and compact-defect proofs before
claiming a genuine primitive cycle.

Likewise, `Canonical/RealCl55SO4EquivariantKasparovCycleBridge.lean` is a finite
certificate surface until it imports and instantiates the primitive cycle.  The
G2 path in `KK/G2IntegratedKasparovEquivarianceBridge.lean` is a separate
equivariance surface and must not be conflated with the generic operator-level
equivariance bridge.

### 10.4 DAG scope correction

The exact path is `lean/DAG/TwoComplexKasparov.lean`.  Its current
`toKasparovCycle` returns only `TargetEnd`, an endomorphism of `DoubledSpace ℝ`,
and is definitionally the identity.  It is therefore an identity-valued
endomorphism placeholder, not a Kasparov-cycle functor.  The surrounding prose
about analytic completion, colimits, and `F² = 1` must be treated as planned
work until separate finite, functorial, colimit, and analytic theorems exist.

The implementation sequence is: finite cell carrier; boundary-derived Dirac
operator; grading anticommutation; bounded/Fredholm data; primitive-cycle
constructor; then functoriality and colimit compatibility.

### 10.5 Bounded-transform and product limits

`RealSplitKreinBoundedTransform` currently takes the compact resolvent as the
phase and stores oddness, Krein-skew-adjointness, and compact square defect as
fields.  The derived compactness lemmas are therefore primitive-cycle
consequences, not a proof of the analytic functional-calculus phase
`D (1 + D²)^(-1/2)`.

`KK/Product.lean` and `KK/Examples.lean` provide product-shaped scaffolding,
not a standard Kasparov product.  A finite composition API must first prove
well-definedness, grading/adjoint compatibility, compact-defect preservation,
associativity, and identity laws before any Kasparov-product terminology is
used.

### 10.6 Machine-checkable non-vacuity

An instance is substantive only if its proofs use the supplied carrier,
representation, grading, and phase data.  Identity actions or identity phases
may be retained as explicitly labelled inhabitation scaffolds, but they do not
count as nontrivial equivariant or geometric realizations.  Every release
candidate must include a source-linked declaration inventory and a narrow Lean
check for each promoted theorem.
