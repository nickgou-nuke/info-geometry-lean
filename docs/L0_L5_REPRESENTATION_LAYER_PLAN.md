# L0-L5 Representation Layer Plan

This plan makes the existing `@[rep_depth ...]` attributes operational in Lean,
Arango, and agent retrieval.

## Current Implementation

- Lean enum: `InfoGeometry.Meta.RepDepth`
- Existing attribute grammar:
  - `@[rep_depth count]`
  - `@[rep_depth projective]`
  - `@[rep_depth operator]`
  - `@[rep_depth krein]`
  - `@[rep_depth transport]`
  - `@[rep_depth thermo]`
- Export tags added by `repDepthTagStringsOf`:
  - `rep_depth:<slug>`
  - `rep_depth_nat:<0..5>`
  - `rep_layer:<L0-L5 label>`
  - `rep_layer_description:<description>`
- `lean/DAG/Indexer.lean` emits these tags in declaration `attrs`.
- `tools/infra/materialize_lossless_infotree.py` lifts them onto Arango raw
  nodes as `rep_depth`, `rep_depth_slug`, `rep_layer`, and labels.
- `tools/infra/arango_gravity_context.py` includes representation-layer fields
  in retrieval scoring and output packets.

## Layer Semantics

- `L0_Count`: counting/combinatorial substrate.
- `L1_Projective`: projection/support/compression substrate.
- `L2_Operator`: operator-algebraic bridge substrate.
- `L3_Krein`: Krein/doubled-geometry substrate.
- `L4_ModularTransport`: modular/transport/flow substrate.
- `L5_ThermodynamicClosure`: thermodynamic/free-energy/closure substrate.

## Next Gates

1. Add a graph audit that reports L5 declarations with no raw witnessed path to
   lower layers.
2. Add retrieval policy knobs:
   - `--prefer-rep-layer`
   - `--require-layer-descent`
3. Add Arango AQL reports:
   - layer counts by module
   - cross-layer edge table
   - suspected layer jumps
4. Promote layer descent results into Hermes packets.

## Reporting

After `dagRefresh` and materialization, run:

```bash
python3 tools/infra/report_rep_layers.py \
  --input-dir artifacts/infotree/arango-lossless-dag \
  --json-out artifacts/infotree/arango-lossless-dag/rep_layers.json
```

The report emits:

- `layer_counts`: number of raw nodes per L0-L5 label.
- `cross_layer_edges`: raw witnessed edge counts between layer labels.
