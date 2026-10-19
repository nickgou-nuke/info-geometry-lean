# Colimit Ledger Protocol

> Status: `current process authority` for colimit ownership and comparison work.
> Scope: how to inventory, classify, canonicalize, and compare the repository's
> colimit-family constructions without creating a third competing owner.
> Rule: the ledger is navigation/audit evidence. Lean owner source, kernel
> checks, and the locked build decide what is proved.

## 1. Artifacts

| Artifact | Path | Role |
|---|---|---|
| Generator | `tools/infra/colimit_ledger.py` | Extracts declarations from repo-owned Lean sources, validates the registry, cross-checks the compiler decl index, emits ledger + report |
| Registry | `tools/data/colimit_registry.json` | Curated owner/comparison/gap records referenced by exact declaration names |
| Ledger (JSON) | `artifacts/colimit_ledger/ledger.json` | Machine-readable ownership graph input |
| Report (MD) | `artifacts/colimit_ledger/LEDGER.md` | Human-readable summary with validation status |

Regenerate:

```bash
python3 tools/infra/colimit_ledger.py
```

## 2. Hard Rules

1. **A `canonical_equiv` edge requires a named Lean declaration.** Semantic
   similarity, shared mathematical content, or matching file names never
   produce an equivalence edge. The generator fails resolution when a registry
   comparison references a declaration that does not exist in the source file.
2. **Universal property means a proved universal property.** A carrier that
   receives a compatible family of maps is a supplied cocone until an owner
   proves `IsColimit`/descent-and-uniqueness. Supplied carriers stay labeled
   `supplied_cocone`.
3. **Different categorical problems are not automatically isomorphic.** Ring
   colimits, Hilbert completions, inverse limits of dual functionals, and
   function-space cylinder unions each need their own comparison statement
   (forgetful functor, comparison morphism, completion map, adjunction).
4. **Retain existing owners until comparison obligations are discharged.**
   Prefer a compatibility re-export over replacing a carrier.
5. **One generic interface.** The generic apex-uniqueness theorem already
   exists (`InfoGeometry.Categorical.TypedCategoryArchetype.colimitCoconePairDatum_apex_inversePair`,
   backed by `InfoGeometry.Canonical.CategoryTheoryConeUniqueness`). New
   "colimit fusion" APIs must re-export it, not rebuild it.
6. **No builds in the ledger run.** `olean_status` is inherited evidence from
   the shared build cache (mtime comparison only). Proof claims still require
   `lake env lean` on the owner file or the locked Lake build.

## 3. Classification Vocabulary

`role` (public surface): `canonical_owner`, `specialization`,
`categorical_preservation`, `apex_uniqueness`, `quotient_realization`,
`inverse_system`, `completion`, `transport`, `supplied_cocone`.

`genuineness`: `genuine_colimit`, `algebraic_direct_limit`,
`quotient_realization_with_universal_property`, `completion`,
`chain_cone_compatibility`, `comparison_isomorphism`, `supplied_cocone`.

A registered entry that fails validation is a maintenance error: the registry
must be corrected or the owner repaired. Do not silence a validation error by
deleting the declaration reference.

## 4. Canonicalization Phases

| Phase | Action | Acceptance criterion |
|---|---|---|
| 1. Inventory | Run the generator; review `candidate_files` | Every candidate file has a qualified owner and provenance |
| 2. Classification | Set `role` + `genuineness` in the registry | No categorical conflation (supplied cocone, quotient, inverse, completion kept distinct) |
| 3. Ownership | Add one `canonical_owner` per category-specific realization | No competing public implementation without a comparison record |
| 4. Comparison | Add comparison record + prove stage-natural mediator | Kernel-checked iso/embedding/readout declaration exists |
| 5. Coherence | Prove comparison triangles/squares commute | Path independence in Lean source |
| 6. Operator transport | Transport star, gradings, traces, states | Exact stage compatibility theorems |
| 7. Deduplication | Replace duplicate use by canonical import + alias | Downstream modules still compile |
| 8. Audit | Pantograph/Lake/axiom/vacuity checks | No new unproved mathematical authority |

## 5. Open Obligations Snapshot

The registry's `gaps` section is the live list; the generator probes the
corpus for possible existing declarations before reporting a gap. As of the
last regeneration:

- module-lane descent uniqueness is only in `SequentialModule`, not in the
  generic `FilteredDirectLimitOwner` module lane;
- `SequentialModule` and `FilteredDirectLimitOwner` overlap on the same
  Mathlib colimit and need a single canonical surface with an alias;
- the Cl(1,1) `limitReadout` is a module readout only; multiplication/star/
  grading coherence (or an isomorphism) is not registered;
- `TensorColimitExpectation.TensorInductiveLimit` is supplied data and must
  not be cited as a universal colimit;
- completed GNS identification needs a compatible isometry with dense range;
- `Ring.DirectLimit` of `DiagAlg` versus the Cantor cylinder representation
  needs a named comparison before any identification claim;
- the split-Clifford `ModuleCat` owner and the Cl(1,1) `DirectLimit` carrier
  need a registered comparison.

## 6. Consumer Discipline

- Before creating a new colimit carrier, search the registry for the lane and
  category; if a `genuine_colimit` owner exists, add a specialization or a
  comparison record instead.
- Downstream modules should import the canonical owner and cite its named
  stage law; avoid unfolding carriers across module boundaries.
- When a comparison is only one-way (embedding, readout, completion map),
  record the direction explicitly in the comparison `notes`; never present a
  one-way map as an equivalence.
