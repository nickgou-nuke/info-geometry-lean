# Conducting Edge Canonicalization

Status: local working doctrine
Authority: Lean source and green builds only
Scope: info-geometry-lean proof-graph canonicalization

## Principle

A purified Lean module can be certified as a conducting edge in the superconducting graph of proofs when its imports, definitions, and theorem chains reduce to mathlib or already-certified local Lean modules.

Once certified, that module may be used as a ladder edge for upward canonicalization of dependent modules.

Arango/DAG evidence remains navigation.  It can identify roots, low-depth targets, replacement frontiers, SCCs, and likely next rungs, but it does not certify truth.  Certification comes from Lean source inspection, explicit theorem/readback lemmas, and green Lean/Lake builds.

## Certification Criteria

A module is conductive only if all criteria hold.

### 1. Purified imports

Allowed:

- Mathlib imports
- Lean/core imports
- Local Lean modules already certified as conducting edges

Not proof authority:

- Markdown doctrine
- handover packets
- external theorem-prover snippets
- arXiv or AFP theorem shapes
- Arango/DAG overlays
- deleted or stale root metadata

### 2. Native proof chains

Definitions and theorems should reduce through Lean-native content:

- Mathlib structures and lemmas
- local structures with explicit field projections
- subtype/existential data with direct extraction lemmas
- constructors with theorem-backed readbacks
- aliases/abbrevs over purified owner modules

A compatibility name may remain, but it must conduct to a native owner rather than preserve a duplicate bridge authority.

### 3. Readback lemmas

Purified modules should expose small theorems that downstream files can use without destructuring internal packaging by hand.

Common readbacks:

- `field_eq` or `[simp]` projection lemmas for structure fields
- `exists_rep` lemmas for subtypes and projective representatives
- `prime_of_mem`, `mem_of_*`, or direct projection lemmas for finite arithmetic roots
- duality or pairing readbacks for cone/operator layers

### 4. Green verification

Minimum checks:

```bash
lake env lean lean/InfoGeometry/Path/Module.lean
```

Then check the nearest downstream consumer:

```bash
lake env lean lean/InfoGeometry/Path/Consumer.lean
```

Then use the build lock for the target modules:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Path.Module InfoGeometry.Path.Consumer
```

## Graph-Guided Workflow

When the root `dag-toolchain.json` is deleted or intentionally dirty, do not restore it just to run diagnostics.  If present, use the venv copy explicitly:

```bash
python3 tools/infra/dag_status.py \
  --config .venv-py312/src/infogeometry/dag-toolchain.json
```

Then inspect derived reports as navigation:

- `reports/dag/replacement-frontier.json`
- `reports/dag/true-root-order.json`
- `reports/dag/theorem-surface-index.json`

Pick a low-level candidate, inspect raw Lean, search usages, and rewrite the smallest truthful layer.

## Rewrite, Do Not Delete

Low-level modules should usually be rewritten rather than removed.

Preferred moves:

- replace duplicate structures with `abbrev` aliases to purified owners;
- keep historical API names if downstream code depends on them;
- add theorem-backed readbacks;
- reduce imports to mathlib or certified local modules;
- validate immediate consumers before moving upward.

Avoid:

- broad namespace deletion;
- replacing proof debt with a larger semantic claim;
- certifying modules that still import uncertified bridge/projection/interface layers;
- treating a DAG edge as a proof edge.

## De Bruijn / tensor-coordinate boundary

De Bruijn coordinates belong primarily to the raw Expr/binder/local-context layer, not to the theorem-dependency DAG itself.  They may annotate tensor-port or binder edges as local, alpha-invariant payload, but they do not replace Arango `_from` / `_to` endpoints and do not certify theorem dependency by themselves.

Keep these edge roles distinct:

- `depends_on`: declaration-level proof dependency exported from Lean/DAG tooling;
- `bound_by`: Expr/local-context binder edge carrying a De Bruijn index;
- `tensor_contraction`: tensor-port relation or candidate computational contraction;
- `conducting_edge`: certification status over a Lean module/declaration path.

The safe readback loop is:

```text
Arango proposes tensor/binder rewrite
  -> Lean checks local scope/port compatibility
  -> Lean theorem evidence/readbacks are checked
  -> Arango records the edge as certified/conductive navigation metadata
```

The first conservative Lean controller for this boundary is `InfoGeometry.Tensor.DeBruijn`.

## Current Certified Examples

### `InfoGeometry.Tensor.DeBruijn`

Conducts through:

- `Mathlib.Data.Nat.Basic`

Provides local, non-semantic readbacks including:

- `TensorPort.index_lt_arity`
- `TensorPort.rawIndex_eq`
- `DeBruijnEdge.source_port_lt`
- `DeBruijnEdge.target_port_lt`
- `DeBruijnEdge.scope_sound`
- `DeBruijnEdge.compatible_of_sound`
- `DeBruijnEdge.sound_of_inScope_compatible`
- `DeBruijnEdge.ofPorts_inScope_iff`
- `DeBruijnEdge.ofPorts_portCompatible_iff`
- `DeBruijnEdge.lift_inScope`
- `DeBruijnEdge.lift_portCompatible`
- `DeBruijnEdge.lift_contractionSound`
- `DeBruijnEdge.lift_shiftSound`

This module certifies local slot/scope payloads directly through lower-module predicates.  It deliberately does not introduce an additional witness package layer, and it does not turn Arango, ML, or tensor-network scores into proof authority.

### `InfoGeometry.Convex.SelfDualCone`

Conducts through:

- `Mathlib.Analysis.Convex.Cone.Dual`
- `Mathlib.Analysis.Convex.Cone.InnerDual`
- `Mathlib.LinearAlgebra.Projectivization.Basic`
- `Mathlib.Topology.Algebra.Module.PerfectPairing`

Provides readbacks including:

- `SelfDualCone.innerDual_eq`
- `ConeRay.exists_rep`
- `ConeInteriorRay.exists_rep`
- `PairedSelfDualCone.isContPerfPair`
- `PairedSelfDualCone.dual_eq_coneF`

### `InfoGeometry.Projective.SelfDualCone`

Conducts upward by aliasing projective-facing names to the convex purified owner:

- `SelfDualCone`
- `ConeInteriorStateSpace`
- `ConeBoundaryRaySpace`

### `InfoGeometry.Algebra.PrimeA1RootSystem`

Conducts through:

- `Mathlib.Data.Finset.Card`
- `Mathlib.Data.Nat.Prime.Basic`

Provides readbacks including:

- `prime_of_mem`
- `prime_of_weyl_coord`
- `mem_cutoff_of_mem_weyl`
- `prime_of_mem_weyl`
- `signature_of_even`
- `signature_of_odd`

## Final Report Template

When certifying a module, report:

```text
Certified conducting edge:
- Module: InfoGeometry.X.Y
- Root chain: Mathlib.A -> Mathlib.B -> InfoGeometry.X.Y
- Readbacks added: theorem_a, theorem_b
- Consumers checked: InfoGeometry.Z.Consumer
- Verification:
  - lake env lean <file>: passed
  - downstream smoke: passed
  - locked build: passed
- Next safe upward rung: InfoGeometry.Z.Consumer
```

## Boundary

Certification of a conducting edge only says that a module is safe as a proof-graph edge.  It does not promote speculative physics, prose doctrine, external theorem-shapes, or semantic overlays into Lean authority.
