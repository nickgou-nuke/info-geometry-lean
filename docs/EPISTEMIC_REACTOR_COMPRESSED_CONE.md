# Epistemic reactor compressed cone

This is the SCC-compressed context packet used before LLM ensemble infusion.

Command:

```bash
lake script run extractCompressedCone -- \
  --decl InfoGeometry.Some.Target.declaration \
  --json-out artifacts/epistemic_reactor/compressed_cone.json \
  --md-out artifacts/epistemic_reactor/compressed_cone.md
```

The packet performs:

```text
raw Lean declaration
  -> SCC component anchor
  -> compressed backward/forward cone
  -> deduplicated quotient edges
  -> raw Lean witness excerpts
  -> ensemble payload
```

Authority boundary:

```text
SCC compression is navigation.
LLM ensemble consensus is proposal.
hive_purified shadow material is not admitted mathematics.
Lean remains proof authority.
Audits remain admission authority.
```

Forbidden jumps:

```text
graph_is_proof
scc_component_is_theorem
ensemble_consensus_is_truth
hive_purified_is_admitted
triple_is_theorem
```

The output includes a `shadow_merge_template`, but it is documentation only.
Actual shadow planting should be handled by a separate gated ingest worker so
that no graph rewrite is confused with theorem promotion.

