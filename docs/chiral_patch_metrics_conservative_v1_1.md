# Chiral Patch Metrics (Conservative v1.1)

This sidecar computes **derived spectral neighborhoods** over the declaration graph.
It does not claim theorem-level Cartan decomposition or physical entanglement.

## Scope
- Input:
  - `artifacts/leantrail/arango/ig_nodes.jsonl`
  - `artifacts/leantrail/arango/ig_edges.jsonl`
  - optional `artifacts/dag/index/expr_fingerprints.jsonl`
- Tool: `tools/infra/build_chiral_patch_hashes.py`
- Output sidecars:
  - `ig_patch_runs.jsonl`
  - `ig_chiral_patches.jsonl`
  - `ig_patch_members.jsonl`
  - `ig_patch_edges.jsonl`
  - `ig_patch_spectral_signatures.jsonl`

## Patch types
- `scc_patch`: SCCs in selected edge graph (cyclic regions; usually trivial on a pure DAG)
- `ego_patch`: k-hop neighborhoods around high-connectivity declarations
- `binder_pattern_patch`: coarse groups by binder/token/redex buckets

## Spectral signature
For each patch we compute on capped node count:
- normalized Laplacian eigenvalues
- first `k` nonzero eigenvalues (bucketed)
- nullity
- pseudo-logdet `sum(log(lambda_i + eps))` over nonzero eigenvalues

## Chiral metrics
- `chiral_entropy`: entropy over forward/backward/mixed orientation proxy
- `chiral_bias`: normalized `(forward - backward) / total`

## Cartan proxy
`cartan_proxy_sector` is annotation-only:
- `k_even`: structure-preserving proxy
- `p_odd`: structure-changing proxy
- `mixed`/`unknown`

These are routing tags, not theorem claims.

## Non-overclaim policy
Do not claim:
- patch hash is spectral determinant
- SCC == proof entanglement in all contexts
- Cartan decomposition theorem established in graph layer

Use wording:
- "derived spectral neighborhood"
- "proxy cartan sector"
- "suggested reusable region"

## Minimal local run

```bash
python3 tools/infra/build_chiral_patch_hashes.py \
  --nodes artifacts/leantrail/arango/ig_nodes.jsonl \
  --edges artifacts/leantrail/arango/ig_edges.jsonl \
  --fingerprints artifacts/dag/index/expr_fingerprints.jsonl \
  --output-dir artifacts/dag/index \
  --print-json
```

The resulting JSONL files are sidecars. They can guide Arango retrieval, but
they do not promote any claim to theorem status.
