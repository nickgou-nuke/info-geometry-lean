# Graph Overlay Implementation Plan

## Decision

Use the external observability pipeline first:

```text
Lean files / optional Lean Expr JSON
  → static declaration/dependency graph
  → alpha-normalized wrapper silhouettes
  → Weisfeiler-Lehman graph hashes
  → JSON / HTML dashboard / ArangoDB ingestion
```

The Lean-native metaprogramming layer comes second. Its purpose is not visualization; it exports elaborated expressions with binder-safe de-Bruijn structure so the external overlay can upgrade from heuristic alpha-normalization to kernel-accurate expression hashing.

## Why external first

1. It works without modifying the Lean project.
2. It does not increase proof-kernel complexity.
3. It can ingest partial or non-compiling files for architectural triage.
4. It supports ArangoDB, D3, Vis.js, graph databases, and batch reports more naturally.
5. It gives immediate namespace-cleanup and dedup guidance.

## Current static result

Scanned root:

```text
/mnt/data/lean
```

Result:

```text
files: 5
declarations: 99
imports: 10
edges: 337
alpha-duplicate classes: 5
WL-duplicate classes: 1
nontrivial lexical SCCs: 1
sorry/admit declarations: 0
axiom/constant/opaque declarations: 0
```

## First dedup findings

1. `CantorCliffordFockBridgeData.car_relations_hold`, `fock_left_inverse`, and `cuntz_isometry_relations` have the same wrapper silhouette. They are theorem re-exports of bridge fields and should probably be grouped under a common “gate re-export” pattern.

2. `finiteBosonicPrimonPartition`, `finiteMobiusFermionicSignedTrace`, and `finiteSupergradedLiouvilleanWittenIndex` are structurally similar finite product/readout definitions. This is expected but should be visually compressed.

3. `KSectorDetOne_true` and `ASectorDetOne_true` are duplicated constant-true sector predicates. These should be consolidated or replaced by actual determinant witnesses when `SL2R_KAN_Model` is bridged to Mathlib `SpecialLinearGroup`.

4. `SplitPrimeCAR.N` and `SplitPrimeCAR.Pi` are structurally similar local CAR readouts but semantically distinct. Do not deduplicate; only visually group.

## Next precision layer

Add a Lean-native exporter:

```text
InfoGeometry/Meta/ExprGraphExport.lean
```

Target export fields:

```json
{
  "name": "Namespace.theoremName",
  "kind": "theorem",
  "typeExprHash": "...",
  "valueExprHash": "...",
  "typeExprDeBruijn": "...",
  "valueExprDeBruijn": "...",
  "constants": ["Nat.add", "Real.log", "..."],
  "universeProfile": "..."
}
```

This will make the WL overlay kernel-aware.

## ArangoDB layer

Recommended collections:

```text
LeanFile
LeanDecl
LeanImport
HashClass
DeferredInterface
```

Recommended edges:

```text
contains: LeanFile → LeanDecl
imports: LeanFile → LeanImport
lexical_ref: LeanDecl → LeanDecl
same_alpha_hash: LeanDecl → HashClass
same_wl_hash: LeanDecl → HashClass
owns_deferred_interface: LeanDecl → DeferredInterface
```

## Closure policy

Every witness/gate must eventually be classified as one of:

```text
local-proof-owned
mathlib-owned
literature-owned
research-open
deprecated/vacuous
```

The graph overlay should make unowned witness gates visible.
