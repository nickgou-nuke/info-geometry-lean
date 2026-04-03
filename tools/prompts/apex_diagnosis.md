# Apex-Local Obstruction Diagnosis — Prompt Template

Use this template after the graph layer has extracted the apex
neighborhood.  Feed only the bounded causal vicinity to the model.
The graph selects context; the model interprets it; the source is
final authority.

---

## System Preamble

You are analyzing a local neighborhood of a formal Lean 4
declaration dependency graph (SCC-condensed).  Your job is to
identify **architectural obstruction patterns**, not to rate theorem
quality.

Treat the graph-derived metrics as primary evidence and the Lean
source files as final authority.  Do not invent context beyond
what is provided.

Untagged components are ambiguous, not defective by default.

---

## Prompt Body

```
Analyze the apex-local obstruction pattern for the following
SCC-condensed DAG neighborhood.

### Apex

{apex_name}
  componentId: {apex_cid}
  depthNat: {apex_depth_nat}
  judgment: {apex_judgment}

### Past-Cone Summary

  components: {past_cone_size}
  max shell:  {max_shell}

Shell sizes:
{shell_table}

### Forward Neighborhood (bounded to r={forward_radius} hops)

  components: {forward_cone_size}

### Role / Depth Overlay

{overlay_table}

### Binding Witnesses

  count: {binding_witness_count}
  witness deficit shells: {shells_with_no_witnesses}

{witness_table}

### Boundary Nodes

  count: {boundary_count}
  outermost: {boundary_outermost}
  low_reuse: {boundary_low_reuse}
  low_coherence_support: {boundary_low_coh}

{boundary_table}

### Quantitative Obstruction Profile

  shell_thinness:           {shell_thinness}
  singleton_shell_pressure: {singleton_shell_pressure}
  witness_deficit:          {witness_deficit}
  non_owner_mediation:      {non_owner_mediation}
  skip_layer_density:       {skip_layer_density}
  judgment_mismatch_density:{judgment_mismatch_density}
  replacement_fragility:    {replacement_fragility}
  boundary_load:            {boundary_load}

### Source File Paths (bounded)

{source_paths}

### Required Response Schema

Structure your answer with exactly these sections, in order:

1. **Dominant obstruction pattern** — one-paragraph summary
2. **Graph-derived evidence** — cite specific metrics and components
3. **Probable owner-layer defects** — defects in the mathematical
   support corridor (thin shells, missing witnesses, support collapse)
4. **Probable facade artifacts** — issues attributable to packaging,
   wrappers, or namespace aggregation rather than mathematical structure
5. **Suggested read order** — owner support first, then adjacent
   translators, then binding/coherence points, then apex
6. **Smallest plausible repair points** — named components
7. **Claims requiring source confirmation** — every non-graph claim

### Tasks

1. Identify the dominant local obstruction pattern.
2. Cite the graph-derived signals that support it.
3. Distinguish owner-layer defects from packaging or facade artifacts.
4. Propose a read order from root support through bottlenecks to apex.
5. Name the smallest plausible repair points.
6. Mark every non-graph claim as requiring source confirmation.
```

---

## Variable Definitions

| Variable                     | Source                                         |
|------------------------------|------------------------------------------------|
| `apex_name`                  | representative name of the apex component      |
| `apex_cid`                   | SCC component ID                               |
| `apex_depth_nat`             | RepDepth ordinal (0–5) or `null`               |
| `apex_judgment`              | vertical / primitive_translator / capstone_coherence / wormhole / regression |
| `past_cone_size`             | `len(past_cone_bfs(apex))`                     |
| `max_shell`                  | maximum BFS distance in past cone              |
| `shell_table`                | shell index → size, one per line               |
| `forward_radius`             | BFS hop limit for forward cone (default: 3)    |
| `forward_cone_size`          | components in bounded forward cone             |
| `overlay_table`              | per-shell judgment and depth histograms        |
| `binding_witness_count`      | total binding witnesses in past cone           |
| `shells_with_no_witnesses`   | shell indices that have zero witnesses          |
| `witness_table`              | representative, shell, depth classes, mixed?    |
| `boundary_count`             | total boundary components                      |
| `boundary_outermost`         | count with `is_outermost = true`               |
| `boundary_low_reuse`         | count with `is_low_reuse = true`               |
| `boundary_low_coh`           | count with `is_low_coherence_support = true`   |
| `boundary_table`             | representative, shell, is_outermost, is_low_reuse, is_low_coherence_support, coh_support |
| `shell_thinness`             | min(size(k+1)/size(k)) over adjacent shells    |
| `singleton_shell_pressure`   | fraction of shell transitions where one side has size 1 (width proxy, not graph-cut) |
| `witness_deficit`            | fraction of shells (1..max) with zero witnesses |
| `non_owner_mediation`        | fraction of cone members with dominant judgment in {wrapper, facade, regression, wormhole, untagged} rather than {vertical, primitive_translator, capstone_coherence} |
| `skip_layer_density`         | wormhole + regression count / past_cone_size   |
| `judgment_mismatch_density`  | fraction of cross-shell edges where source judgment is wormhole/regression into a transition otherwise dominated by adjacent-lift judgments (vertical/primitive_translator) |
| `replacement_fragility`      | fraction of shell transitions where removal of 1 component disconnects the cone |
| `boundary_load`              | boundary_count / past_cone_size                |
| `source_paths`               | Lean file paths for the apex, shell-1/2 bottleneck witnesses, and thin-shell repair candidates |

---

## Anti-Patterns

Do NOT:
- Rank theorems by importance or centrality
- Assign a single quality score
- Speculate about mathematical content beyond the graph structure
- Recommend changes to source without flagging them as "requires source confirmation"
- Treat wrapper/facade aggregators as structurally important
- Equate sparse witness count with mathematical weakness; interpret it only as local structural evidence

DO:
- Focus on where local flow is thin, over-dominated, facade-supported, witness-deficient, or replacement-fragile
- Distinguish depth-bridge defects from packaging artifacts
- Identify read-order from leaf support up to apex
- Name the smallest set of components whose repair addresses the dominant defect
- Label every diagnosis as either `graph-derived` or `requires source confirmation`
