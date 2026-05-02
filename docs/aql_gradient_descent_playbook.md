# AQL Gradient-Descent Playbook (Conservative)

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

Purpose: rank derived spectral neighborhoods (patches) and pick one formalization target.
No theorem-level claims are made by these queries.

## Queries
- `tools/infra/aql/chiral_patch_gradient_top_clusters.aql`
- `tools/infra/aql/chiral_patch_select_formalization_target.aql`
- `tools/infra/aql/chiral_patch_blocker_edges_for_decl.aql`
- `patch.maxent_style_candidates` in `src/igf/graph/query_registry.py`

## Step 1: Top clusters

Use bind vars (defaults shown):
- `runId`: latest run if omitted
- `limit`: `5`
- `wClosureDebt`: `0.45`
- `wCrossModule`: `0.25`
- `wLowReuse`: `0.20`
- `wChiral`: `0.10`

Example (arangosh):

```javascript
const q = require('fs').readFileSync('tools/infra/aql/chiral_patch_gradient_top_clusters.aql', 'utf8');
db._query(q, {
  limit: 5,
  wClosureDebt: 0.45,
  wCrossModule: 0.25,
  wLowReuse: 0.20,
  wChiral: 0.10
}).toArray();
```

## Step 2: Pick one E9/Langlands candidate set from top patch

Bind vars:
- `patchKey`: selected `patch_key` from step 1
- `moduleRegex`: `(E9|Langlands|Automorphic|Cartan|KacMoody)`
- `limit`: `25`

```javascript
const q2 = require('fs').readFileSync('tools/infra/aql/chiral_patch_select_formalization_target.aql', 'utf8');
db._query(q2, {
  patchKey: 'patch_run_...__ego_patch_...__patch_...',
  moduleRegex: '(E9|Langlands|Automorphic|Cartan|KacMoody)',
  limit: 25
}).toArray();
```

## Step 3: Extract blocker edges for one declaration

Bind vars:
- `declId`: `ig_nodes/<declaration-key>`
- `maxHops`: `2`
- `limit`: `200`

```javascript
const q3 = require('fs').readFileSync('tools/infra/aql/chiral_patch_blocker_edges_for_decl.aql', 'utf8');
db._query(q3, {
  declId: 'ig_nodes/InfoGeometry....',
  maxHops: 2,
  limit: 200
}).toArray();
```

## Interpretation rules
- `closure_debt_density` is a structural proxy (`1 - theorem_ratio`), not a proof of debt.
- `chiral_pressure` is routing-only (`abs(chiral_bias) * chiral_entropy`).
- `patch.maxent_style_candidates` is a Jaynes/MaxEnt-inspired retrieval
  proxy over derived sidecars. It is not evidence for RH, primitive-set
  extremality, or a theorem-level thermodynamic claim.
- `patch.maxent_candidate_ground_states` remains as a compatibility alias, but
  new tooling should use the safer `patch.maxent_style_candidates` ID.
- Rankings suggest priority neighborhoods; Lean proofs remain the authority.
