# Chiral Patch Metrics (Conservative v1.2)

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
- `ego_patch`: undirected k-hop neighborhoods around high-connectivity declarations
- `binder_pattern_patch`: coarse groups by binder/token/redex buckets

## Spectral signature
For each patch we compute on a deterministic capped node set:
- normalized Laplacian eigenvalues
- first `k` nonzero eigenvalues (bucketed)
- nullity
- pseudo-logdet `sum(log(lambda_i + eps))` over nonzero eigenvalues
- `spectral_status`, which is `exact`, `truncated`, `trivial`, or `failed`

For conservative v1.2 the directed local graph is symmetrized before spectral
analysis:

```text
A_sym(i,j) = weight(i -> j) + weight(j -> i)
L_norm = I - D^{-1/2} A_sym D^{-1/2}
```

Isolated nodes contribute to nullity and are handled without division by zero.
Large patches use sparse low-eigenvalue approximation instead of densifying the
entire local graph.

## Patch graph
`ig_patch_edges.jsonl` contains:

- internal patch-edge traces for local auditing
- patch-to-patch dependency edges derived from declaration edges crossing patch
  memberships

The cross-patch `affinity` is a normalized routing score, not a proof metric.

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

Every row carries a schema/version marker. Patch `coarse_hash` values are
content-addressed from canonical patch features and exclude run IDs and
timestamps, so repeated runs over the same graph preserve coarse hashes. The
run `source_graph_hash` covers nodes, edges, and the optional fingerprint file.

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
