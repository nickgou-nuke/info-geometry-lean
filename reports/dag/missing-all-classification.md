# Remaining `All` Coverage Classification

This report classifies the declaration-bearing Lean files that are still outside the authoritative `InfoGeometry.All` export graph.

## Summary
- declaration-bearing source files: `617`
- declaration-index files covered by current export root: `615`
- remaining missing declaration-bearing files: `2`

## Buckets
### Absorb Directly Into `Canonical.All` (0)
- none

### Absorb Directly Into `InfoGeometry.All` (0)
- none

### Absorb Via Branch Façade (0)
- none

### Namespace / Attribution Fix Needed (0)
- none

### Duplicate / Shadow Candidate (0)
- none

### Keep Out Of `All` (0)
- none

### Manual Review (2)
- `lean/InfoGeometry/Exploration/Symphony/Basic.lean`
  namespace: `InfoGeometry.Exploration.Symphony`
- `lean/InfoGeometry/Exploration/Symphony/Draft.lean`
  namespace: `InfoGeometry.Canonical.SymphonyAttention`

## Notes
- This report is a canonicalization plan, not a proof of semantic validity; every listed file already compiles in the default `InfoGeometry` library build.
- Files under `lean/InfoGeometry/Unstable/` are treated as quarantine and excluded from the authoritative `InfoGeometry.All` coverage metric.
- Legacy scaffolding such as the old GraphExport compatibility lane and dummy fixture modules were archived out of `lean/InfoGeometry` in favor of the authoritative `artifacts/dag` pipeline.
- Files under `namespace_or_attribution_fix` are not clean umbrella omissions; at least part of the problem is that their public declarations live under a shifted namespace or are poorly attributed by the declaration exporter.
