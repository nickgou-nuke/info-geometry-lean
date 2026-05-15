# Lean-to-JSON sidecar design for content-addressable GraphRAG

This overlay extends the existing `lean/DAG/ExprArangoExport.lean` pipeline.
It should not replace `ig_nodes` / `ig_edges`.

## Authority boundary

Lean remains proof authority.  Arango stores derived navigation, exact hash
addresses, concept links, and public audit lineage.

Hash equality can propose reuse or duplication.  It cannot promote theorem
equivalence to rewrite authority.  Rewrite authority remains in the Lean/kernel
certificate lane.

## Hash modes

The sidecar should emit explicit normalization metadata for every hash.

Recommended modes:

- `rawExprHash`: normalized serialization close to the kernel expression.
- `alphaExprHash`: binder-name-insensitive expression hash using de Bruijn indices.
- `patternExprHash`: owner-name-relaxed theorem-pattern hash.
- `typeHash`: declaration type/statement hash.
- `valueHash`: declaration body/proof-term hash, when available.
- `typeSubhash`, `valueSubhash`, `proofSubhash`: hashes of sub-expressions used for overlap search.

Do not use cryptographic hashes directly as cosine vectors.  Hashes are exact
content addresses.  Approximate theorem discovery uses `logicVector`: a
deterministic dense feature-hash vector built from the multiset of sub-expression
hashes.

## Export row sketch

```lean
structure HashExportRow where
  declName : String
  moduleName : String
  kind : String
  typeHash : String
  valueHash? : Option String
  typeSubhashes : Array String
  valueSubhashes : Array String
  normalization : String
  leanVersion : String
  quality : String
```

## Minimum metadata

Every hash record should carry:

```json
{
  "leanVersion": "4.x",
  "mathlibVersion": "...",
  "normalization": "deBruijn-alpha-no-mvar-no-synthetic-sorry",
  "transparency": "reducible|semireducible|instances|none",
  "universePolicy": "preserve|erase",
  "proofPolicy": "include|type-only"
}
```

## Two required normalizations

`debruijn-v1-owner-aware`

Preserves fully qualified constants.  Use for dependency hygiene and exact
owner-surface audit.

`debruijn-v1-pattern`

Relaxes constants to normalized type/shape hashes.  Use for theorem-pattern
discovery when the same logical form appears under different owners.

## First 15 seed modules

Start with the sealed corridor:

```text
InfoGeometry.Canonical.DrazinLightConeDictionary
InfoGeometry.Canonical.InverseKernelAlgebra
InfoGeometry.Canonical.DrazinHodgeChiralBridge
InfoGeometry.Canonical.SuperchargeModularHamiltonianBridge
InfoGeometry.Canonical.SouriauModularHamiltonianBridge
InfoGeometry.Canonical.BoundedModularFlowCalibration
InfoGeometry.Krein.HestenesModularKMSBridge
InfoGeometry.Krein.HestenesKreinVacuumBridge
InfoGeometry.Canonical.StandardFormOmegaVolumeBridge
InfoGeometry.Krein.HestenesConnesWilsonBridge
InfoGeometry.Krein.HestenesMoebiusClosureBridge
InfoGeometry.Krein.HestenesD4HurwitzBridge
InfoGeometry.Krein.HestenesCPTONNDualityBridge
InfoGeometry.Krein.HestenesAffineO55ClosureBridge
InfoGeometry.External.Virasoro.VirasoroAlgebra
```

## First audit question

```text
Why is the O(5,5) / Cl(5,5) affine extension witness-gated rather than an automatic theorem?
```

The expected path should touch:

```text
concept_o55_affine_closure
-> HestenesAffineO55ClosureBridge.affine_closure_requires_O55
-> principle_witness_gated_affine_o55
-> principle_lean_is_authority
```
