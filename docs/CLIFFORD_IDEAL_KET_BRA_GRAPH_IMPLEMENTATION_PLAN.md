# Clifford ideals, ket–bra reconstruction, and structural graph implementation plan

Date: 2026-10-31
Status: proposed implementation; source inspection completed, no fresh build performed

## Objective

Connect the existing tensor-quotient, Clifford, principal-ideal, spinor, and
dyadic constructions through explicit typed maps and compatibility theorems.
Expose those declarations and their dependencies in a provenance-preserving
graph so recurring algebraic structures can be investigated without treating
graph similarity as mathematical equivalence.

The main concrete carrier is the native real `Cl(5,5)` algebra and its actual
vacuum ideals. Reuse the existing categorical infrastructure for any later
colimit extension. This plan does not replace algebraic owners with matrices,
introduce an analytic completion, or equate independent Clifford realizations
without an intertwining theorem.

## Existing implementation to reuse

| Concern | Owner and inspected declarations |
| --- | --- |
| Tensor algebra | `lean/InfoGeometry/Algebra/TensorAlgebraCanonical.lean`: `includeLinear`, `liftLinear`, uniqueness, induction, `tensorAlgebraEquivTensorPowerSum` |
| Clifford quotient | Installed Mathlib `LinearAlgebra/CliffordAlgebra/Basic.lean`: `Rel`, generated ring congruence, quotient carrier, `TensorAlgebra.toClifford` |
| Generic ideals and pairing | `lean/InfoGeometry/Clifford/CliffordIdealReadback.lean`: `LeftIdeal`, `RightIdeal`, action closure, `corner_pairing_mem` |
| Corner and commutant | `lean/InfoGeometry/Algebra/IdempotentCornerCommutant.lean`: `PrincipalLeftIdeal`, `leftAction`, `rightCornerAction`, `cornerEquivLeftIdealCommutant`, multiplication-order theorem |
| Native Clifford/matrix equivalence | `lean/InfoGeometry/Clifford/Cl55SpinorAlgebraEquiv.lean`: `cl55SpinorAlgEquiv` |
| Vacuum left ideal | `lean/InfoGeometry/Clifford/Cl55VacuumIdealSpinorBridge.lean`: `cl55VacuumIdealSpinorEquiv`, dimension 32, action intertwining |
| Vacuum right ideal and transpose | `lean/InfoGeometry/Clifford/Cl55VacuumIdempotentIdeal.lean`: `MinimalRightIdeal`, `transposeCl55`, `rightIdealToLeftIdeal`, dimension 32, wedge/contraction and CAR action results |
| Dyadic reconstruction | `lean/InfoGeometry/Clifford/Cl55DyadicMoritaBridge.lean`: `ketBra`, `dyadic_span_top`, `cl55_eq_sum_dyadic` |
| Separate polar example | `lean/InfoGeometry/Canonical/ZornPolarKetBra.lean`: endomorphism-valued dyads, composition, adjoint pairing, trace, square-zero and idempotence criteria |
| Graph primitives | `lean/DAG/Basic.lean`, `TermDigest.lean`, `ContentAddressable.lean`, `RawInfoTreeExport.lean`; `tools/infra/batch_raw_infotree_export.py` |

This inventory records inspected source, not current kernel certification or
an exhaustive absence audit. A declaration name containing “minimal” is not
evidence that simplicity of the module has been separately established.

## Phase 1 — Confirm exact theorem contracts and reuse

1. Follow `docs/REPO_DEEP_SEARCH_PROTOCOL.md` across alternate names, actual
   carriers, imports, and consumers before identifying any missing theorem.
2. Search for existing corner algebra instances, opposite-algebra equivalences,
   ideal duality, scalar corner readouts, primitive-idempotent results, and
   simple-module instances. Inspect their hypotheses and proof dependencies.
3. Compare the two concrete matrix realizations used by the vacuum-ideal and
   dyadic owners. Record their coordinate bases and transition maps. Do not
   assume their images of the vacuum idempotent or basis dyads coincide.
4. For each confirmed gap, record the precise Lean signature, carrier, field,
   hypotheses, reused declarations, downstream consumers, and excluded claims.

Deliverable: a source-linked contract table distinguishing existing theorem,
existing theorem needing an adapter, and confirmed implementation gap.

## Phase 2 — Package the generic ideal pairing and actions

Work over an associative unital algebra `A` over a commutative ring `R`, with
an explicit idempotent `e`. Reuse the existing fixed-point models of `Ae` and
`eA` and the supported corner `eAe`.

Implement only missing API:

- Linear/submodule packaging of the right ideal matching the left-ideal API.
- The bilinear pairing `eA × Ae → eAe`, induced by multiplication.
- The bilinear outer product `Ae × eA → A`, also induced by multiplication.
- Compatibility `(x * y) * z = x * (y * z)` with the appropriate ideal and
  corner carriers. Preserve the order of all noncommutative products.
- The relation between the left action and right corner action.
- If useful to consumers, upgrade the existing carrier equivalence with the
  commutant to an algebra equivalence from the opposite corner, after checking
  available instances. Do not duplicate the existing range/injectivity proofs.

Keep new helper modules small. Do not enlarge the existing vacuum compatibility
file with unrelated generic algebra. Choose final filenames after the reuse audit.

Acceptance: all maps have truthful types, their underlying functions are the
existing multiplication/actions, and the composition-order laws are explicit.

## Phase 3 — Connect actual Cl(5,5) kets and bras

Use the existing nonzero vacuum idempotent and its principal ideals.

1. Construct or reuse an explicit scalar corner identification `eAe ≃ₐ[ℝ] ℝ`
   through the vacuum owner's rank-one coordinate projection.
2. Package the resulting scalar bilinear pairing between right and left ideals.
3. Prove nondegeneracy in both arguments, preferably through the existing
   coordinate equivalences; expose the resulting right-ideal/dual-left-ideal
   linear equivalence if absent.
4. Record transpose as the existing real anti-involution connecting these
   ideals. Prove pairing compatibility with it at the actual chosen coordinates.
5. Audit minimality separately. If absent, prove simplicity as an `A`-module
   using the faithful full endomorphism representation and transport it to
   the ideal. Do not confuse simplicity as an `A`-module with simplicity as
   a real vector space. State the right-module result over the opposite algebra.

Acceptance: scalar pairing and ideal duality are explicit, with any minimality
claim backed by a dedicated declaration. Complex Hermitian conjugation and
positivity require separate contracts; they are not consequences of real transpose.

## Phase 4 — Identify ideal products with the existing dyads

1. Construct the ket and bra embeddings from the coordinate spinor and its dual
   into the actual left and right ideals.
2. Prove that their product maps to the expected outer-product matrix under
   the vacuum owner's matrix equivalence.
3. Reconcile this equivalence with `cl55SpinorAlgEquiv` by an explicit proved
   coordinate change before connecting to `cliffordDyadicAtom`.
4. Derive the rank-one composition identity from the generic pairing:
   `(ket ψ * bra φ) * (ket u * bra v) = ⟨φ,u⟩ • (ket ψ * bra v)`.
5. Reuse `cl55_eq_sum_dyadic` to obtain ideal-product reconstruction and spanning.
   Avoid reproving matrix spanning in a second owner.

Acceptance: a commuting diagram connects native Clifford elements, actual ideal
members, spinor coordinates, and dyadic matrices. “Morita” terminology must be
scoped: a spanning theorem alone is not a categorical equivalence of module categories.

## Phase 5 — Extract the construction as a typed graph

Start with a bounded extraction of these owners and their dependency closure.
Read existing graph manifests before considering a refresh.

- Preserve declaration identity independently of content fingerprints.
- Keep type dependencies and body dependencies distinct.
- Link expressions to declarations, source locations, module identities, and
  environment/toolchain fingerprints. Record unavailable bodies explicitly.
- Preserve expression argument order, binders, universes, and local contexts.
  Use relation/operation occurrence nodes with labelled ports for incidence views.
- Link captured InfoTree records as elaboration provenance; do not infer a full
  tactic history from `.olean` declarations. Preserve exporter leakage records.
- Distinguish direct compiler references from derived semantic annotations such
  as “corner pairing” or “ideal reconstruction”; attach theorem witnesses to
  every claimed mathematical compatibility edge.
- Produce a coverage manifest listing requested modules, successes, failures,
  exclusions, stale source/build matches, and unresolved references.

Acceptance: every displayed algebraic relationship can be traced to its exact
declaration and hypotheses. A “total graph” claim is relative to the manifest,
not to the successful import of a single umbrella module.

## Phase 6 — Investigate scales and recurring constructions

Use the verified ideal–corner–pairing–endomorphism pattern as an initial example.

1. Compute SCC condensation separately for selected dependency relations.
2. Inspect multi-apex dependency cones for the quotient, vacuum ideal, pairing,
   commutant, and reconstruction theorems.
3. Compare typed motifs, bipartite co-clustering, and multiresolution communities.
   Control ubiquitous library dependencies and compare against namespace baselines.
4. Measure stability under resolution and edge-weight changes. Preserve mappings
   from all clusters back to original declarations.
5. Use diffusion/embedding views only for navigation; require explicit maps and
   Lean theorems before identifying two mathematical constructions.

Acceptance: candidate archetypes come with graph witnesses and source readback,
not automatic theorem-equivalence or physical-interpretation claims. No manifold
or continuum construction is inferred merely from an embedding.

## Verification and execution discipline

- Read the canonical pipeline and applicable proof skills before implementation.
- Preserve pinned dependencies; never run `lake clean` or delete build caches.
- Inspect compiler/test processes before verification. Run builds sequentially
  through `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock <targets>`.
- Check focused owners first, then affected consumers and required repository gates.
- Audit new declarations and their dependencies for placeholders, custom axioms,
  vacuous hypotheses, and accidental carrier changes. Successful elaboration alone
  does not establish that the theorem matches its intended interpretation.
- Stage edits immediately, preserve unrelated work, and record source identities
  with verification results. Do not modify dirty external submodules.

## Suggested first implementation increment

Complete Phase 1, then package only the generic bilinear corner pairing and its
outer-product action compatibility from Phase 2 if they are confirmed gaps.
Verify those owners and consumers before proceeding to the Cl(5,5) coordinate
comparison. Full graph extraction and clustering follow the proved algebraic
connections; they are not prerequisites for the first proof increment.
