# Epistemic Reactor Shadow Plant Worker

`tools/infra/shadow_plant_worker.py` is the gated mutation step after ensemble
infusion.

It consumes an `ensemble_consensus.json` proposal packet and plants the result
into separate ArangoDB shadow collections:

```text
hive_purified_shadow_batches
hive_purified_shadow_nodes
hive_purified_shadow_edges
```

## Authority boundary

Planted rows use:

```json
{
  "authority": "hive_purified",
  "promotion_state": "shadow_only"
}
```

This is not proof authority. Shadow rows are navigation and scheduling material
only. Promotion still requires Lean, build, audit, and promotion-decision
packets.

Forbidden jumps:

```text
ensemble consensus -> theorem truth
hive_purified shadow -> Lean proof
graph planting -> audit admission
```

## Dry run

```bash
lake script run shadowPlantWorker -- \
  --input artifacts/reactor/ensemble_consensus.json \
  --dry-run \
  --json-out reports/dag/shadow-plant-worker.json
```

## Mutating run

Run the dry run first. Then:

```bash
lake script run shadowPlantWorker -- \
  --input artifacts/reactor/ensemble_consensus.json \
  --json-out reports/dag/shadow-plant-worker.json
```

The worker is idempotent for the same consensus packet: it uses deterministic
keys and does not delete raw graph material.

## Accepted input

The input packet must keep the ensemble authority boundary:

```json
{
  "schema": "info_geometry.epistemic_reactor.ensemble_consensus.v1",
  "authority": "proposal",
  "authority_boundary": {
    "consensus_is_not_truth": true,
    "lean_remains_proof_authority": true
  }
}
```

The worker rejects packets that claim promoted authorities such as
`lean_checked`, `build_checked`, `audit_checked`, or `promoted`.
