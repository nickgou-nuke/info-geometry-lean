# Colimit and Inverse-Limit Ontology, Taxonomy, and Source Lineage

## Scope and evidence

This map describes repo-owned Lean constructions found in the current checkout. It is a navigation
and architecture document, not a proof certificate. Lean owner declarations and their hypotheses
remain authoritative. The current bounded filename scan
`rg --files lean/InfoGeometry | rg '(Colimit|DirectLimit|InverseLimit|ProjectiveLimit)'`
returned 664 paths; the pattern is a filename heuristic, includes overlapping concepts, and is not
a count of distinct mathematical constructions or a complete inventory.

The main synthesis owner is
[`InductiveCategoricalColimitInverseLimitUnificationPoset.lean`](../lean/InfoGeometry/Canonical/InductiveCategoricalColimitInverseLimitUnificationPoset.lean).
It composes existing owners and proves finite-stage bridge statements. A second integrated owner,
[`ColimitInverseLimitOntologyTaxonomyPhylogenesisPoset.lean`](../lean/InfoGeometry/Canonical/ColimitInverseLimitOntologyTaxonomyPhylogenesisPoset.lean),
contains complementary explicit-setoid duality and conditional retraction/section results. Its
ranked DAG is a curated formal ordering, not Git phylogeny. The source history below is limited to
selected owner paths and representative commits; it is not a complete repository history.

## Ontology: carriers and maps

### 1. Concrete directed quotient and categorical colimit

For a directed family of modules with compatible linear transition maps, the repo constructs both
the concrete `AddCommGroup.DirectLimit` quotient and the categorical colimit in `ModuleCat R`.
`FilteredDirectInverseColimit.lean` owns the diagram, cocone, descent map, and the concrete-to-
categorical bridge. The synthesis owner verifies agreement on stage representatives and on the
specified inductive cocone.

The `JaynesianColimitCarrier` quotient has a proved equivalence to Mathlib's noncommutative
`DirectLimit` for the same sequential star-ring system (`jaynesianCarrierEquivMathlibDirectLimit`).
The quotient itself is only a `Type`; the equivalence transports no ring instance onto that quotient
by itself. Separately, `InductiveCategoricalColimitInverseLimitUnificationPoset` relates
`AddCommGroup.DirectLimit` to the categorical `ModuleCat` colimit on finite-stage representatives
and proves compatibility with a specified cocone. These are related carrier/universal-property
bridges, not one blanket identification of ring-category and module-category colimits.

There is also a distinct categorical **RingCat** lane. `Categorical/FilteredDirectLimitOwner.lean`
owns generic ring-colimit descent and uniqueness (`descendDirectLimitRing`). For the concrete
noncommutative Cuntz matrix tower, `CuntzMatrixRingModuleComparisonBridge.lean` proves a ring
equivalence between its explicit algebraic carrier and Mathlib's native `RingCat` colimit
(`algebraicCarrierRingEquiv`), with stage compatibility, then transports the star operation and
trace readout. This is a tower-specific construction. It does not prove a universal equivalence
between arbitrary `RingCat` and `ModuleCat` colimits; the latter comparison is separately linear
and depends on the given underlying module diagram.

### 2. Algebraic dual of an inductive system

`FilteredDirectInverseColimitReadback.lean` owns the contravariant diagram of algebraic dual
modules, its categorical limit, and the readback maps. A transition `A i →ₗ[R] A j` induces the
reverse map `Hom(A j, R) →ₗ[R] Hom(A i, R)` by precomposition. Thus a compatible family of stage
functionals is a cone over the opposite diagram.

The owner proves the correspondence between:

- compatible families of stage functionals;
- morphisms out of the inductive colimit into `R`;
- elements of the categorical limit of the dual modules.

This is the algebraic universal-property statement `Hom(colimit Aᵢ, R) ≃ limit Hom(Aᵢ, R)` in the
formalized setting. It is not a claim about continuous duals, Hilbert adjoints, reflexivity, or a
topological duality theorem.

### 3. Projective systems of spaces and cylinder observables

The synthesis owner defines pullback maps on function modules. A restriction map `X j → X i`
induces `X i → R → X j → R`; a compatible projective cone therefore gives an inductive cocone of
observable modules. The descended map evaluates a stage observable at the corresponding projected
point.

This constructs a map out of the observable colimit. In general it does **not** prove that every
function on the inverse-limit space is a cylinder function, nor that this map is an isomorphism.
Such a result needs additional hypotheses and a separate proof.

The Cantor/UHF specialization uses the `TopCat` limit of finite prefix spaces and proves the
compatibility of cylinder observables with the UHF diagonal successor embedding. The source owners
are `UHFInductiveColimitBoundaryInverseLimit.lean`,
`CantorProjectiveLimitCategoricalIsoTopCat.lean`, and the synthesis module.

### 4. Topological limits and filtered–finite interchange

`FilteredTopologicalDirectInverseColimit.lean` owns topological direct- and inverse-limit
constructions. In a different lane, `Holonomy.lean` exposes Mathlib's filtered-colimit/finite-limit
isomorphism for diagrams in `ModuleCat`, with the hypotheses that the limit shape is finite and the
colimit indexing category is filtered. This is not an unrestricted interchange law for arbitrary
limits and colimits.

### 5. Operator and trace applications

The Peirce/Cartan/Gauss–Bonnet and `Cl(1,1)` owners instantiate the algebraic machinery with
noncommutative operator algebras and compatible trace functionals. The synthesis theorem transports
the stated stage identities through the constructed dual readbacks. These results do not by
themselves construct a completed operator algebra, a continuous trace on a completion, an analytic
index theorem, or a geometric Gauss–Bonnet theorem.

## Taxonomy: distinct clades

| Clade | Repo-owned lane | Mathematical role | Boundary |
|---|---|---|---|
| Concrete direct limits | `FilteredDirectLimitOperator`, `FilteredDirectInverseColimit`, `JaynesianNilpotentInductiveColimitPoset` | Eventual-equality quotient; proved equivalence to Mathlib's algebraic `DirectLimit`; separate additive direct-limit/module-colimit comparison | Quotient has no ring structure merely from its `Type` definition; the two category carriers are not asserted identical |
| Categorical module colimits | `FilteredDirectInverseColimit` | `ModuleCat` diagram, colimit cocone, universal descent | Requires the stated directed-system hypotheses |
| Categorical ring colimits | `Categorical/FilteredDirectLimitOwner`, `CuntzMatrixRingModuleComparisonBridge` | Generic RingCat descent plus a concrete noncommutative Cuntz-tower equivalence to its explicit algebraic carrier | The explicit ring equivalence and trace/star transport are for that tower; no blanket RingCat/ModuleCat identification |
| Dual projective limits | `FilteredDirectInverseColimitReadback` | Opposite diagram of algebraic duals and compatible functional families | Not continuous/topological duality |
| Topological inverse limits | `FilteredTopologicalDirectInverseColimit`, Cantor boundary owners | Limits in `TopCat`, finite-prefix projections | Does not imply every observable is a cylinder observable |
| Cylinder observable systems | Main synthesis owner; UHF diagonal owners | Pullback turns inverse restrictions into direct observable maps | A compatible cocone map is not automatically an isomorphism |
| Filtered/finite interchange | `Categorical/Holonomy.lean` | Filtered colimit commutes with finite limits in the formalized module setting | Finite-shape and filteredness assumptions are essential |
| Operator/trace realizations | `Cl11FilteredDirectInverseColimit`, Peirce and Gauss–Bonnet owners | Noncommutative stage identities and compatible trace readback | No automatic analytic completion or index theorem |
| Retraction/section systems | `ColimitInverseLimitOntologyTaxonomyPhylogenesisPoset.lean` | A retraction law gives injective upward maps, surjective downward maps, and an idempotent coarse-graining composite | Conditional abstract tower; does not construct a conditional expectation |
| Explicit setoid colimit duality | Same owner; `JaynesianNilpotentInductiveColimitPoset.lean` | Compatible functionals on a quotient colimit correspond to inverse-compatible stage functionals | Function-level quotient bridge and conditional ring cone transfer are distinct from `ModuleCat` colimits |

## Causal dependency graph

The synthesis owner’s eight stages encode the following direct dependencies. The graph is a DAG;
the stage numbers supply a topological ranking, not an assertion that each neighboring pair has a
direct edge.

```text
C1: concrete quotient ↔ categorical module colimit ───────────┐
C2: dual opposite diagram → C3: dual readback/equivalence ─→ C7: operator trace application ─┐
C4: projective spaces → cylinder observables → C5: Cantor/UHF specialization ───────────────┤
C6: filtered-colimit/finite-limit interchange ────────────────────────────────────────────┤
                                                                                             ▼
                                                              C8: master synthesis
```

The Lean relation `ColimitInverseLimitUnificationStage.causalEdge` records the direct edges and
proves that each increases the rank; transitive paths therefore cannot form a cycle. The separate
`ColimitDevelopmentStratum.rankEdge` and legacy-named
`ColimitPhylogeneticEpoch.causalEdge` are curated formal rankings/graphs. Neither relation is a Git
commit graph or a claim of chronological ancestry.

## Phylogenesis: bounded source-history observations

The following are representative commits visible in the selected owner-path history. They show
several strands converging; they do not establish a complete chronological taxonomy for the whole
repository.

| Date | Commit | Source-history signal |
|---|---|---|
| 2026-08-19 | `54ec9507d` | QuantumGeometry projective compatibility layer |
| 2026-09-06 | `212e57e86` | Cantor/KMS cylinder-state restoration and audit import repair |
| 2026-10-20 | `bafd60d55` | Dual colimit and projective-limit work |
| 2026-10-21 | `b025186df` | Projective-limit and reverse-mode laws |
| 2026-10-31 | `144f51c8d` | Staged proof-gate repairs and audit integration |

Earlier and adjacent direct-limit, superclosure, Clifford, and faithful-embedding work exists in
other paths. The table intentionally reports only commits observed in a bounded path query; commit
dates describe repository history, not a mathematical dependency order. The Lean causal graph above
is the formalized dependency claim.

## Reproducible inspection commands

Run these from the repository root to refresh the bounded observations:

```bash
rg --files lean/InfoGeometry | rg '(Colimit|DirectLimit|InverseLimit|ProjectiveLimit)'
rg -n 'dualModuleDiagram|dualInverseFamilyToProjectiveLimit|colimitFunctionalStageFamily' lean/InfoGeometry/Canonical
rg -n 'colimit_limit_iso|filteredColimitFiniteLimitIso' lean/InfoGeometry/Categorical lean/InfoGeometry/Canonical
git log --format='%h %ad %s' --date=short -- lean/InfoGeometry/Canonical/FilteredDirectInverseColimit.lean lean/InfoGeometry/Canonical/FilteredDirectInverseColimitReadback.lean lean/InfoGeometry/Canonical/FilteredTopologicalDirectInverseColimit.lean lean/InfoGeometry/Categorical/Holonomy.lean lean/InfoGeometry/Canonical/UHFInductiveColimitBoundaryInverseLimit.lean
```

The filename scan is navigation only. Read declarations, hypotheses, proofs, and consumers before
using any result as mathematical evidence.
