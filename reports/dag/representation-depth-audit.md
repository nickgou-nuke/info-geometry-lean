# Representation Depth Audit

Direct file-to-file dependency audit over the authoritative declaration DAG, scored against Lean-exported representation-depth tags with the manual index retained for file roles and notes.

## Status
- topological integrity gate: **PASS**
- edge semantics: direct declaration dependencies lifted to owner-file edges
- depth semantics: each tracked file is an interval `[source_depth, target_depth]`
- rule: a direct dependency may stay within the same interval or touch the immediately previous layer only

## Sources
- manual role index: `reports/dag/representation-depth-index.json`
- Lean depth export: `artifacts/dag/representation-depth-tags.json`
- manual indexed files: `20`
- Lean-tagged files: `16`
- Lean-tagged declarations: `18`

## Counts
- merged indexed files: **23**
- indexed files seen in authoritative graph: **23**
- tracked file edges: **46**
- healthy direct edges: **46**
- wormholes: **0**
- regressions: **0**
- offending source files: **0**

## Indexed Inventory
### Kinds
- `coherence`: `4`
- `mixed`: `1`
- `owner`: `9`
- `translator`: `9`
### Intervals
- `0→1`: `1`
- `1→1`: `4`
- `1→2`: `1`
- `2→2`: `2`
- `2→3`: `2`
- `2→4`: `1`
- `3→3`: `4`
- `3→4`: `4`
- `4→5`: `1`
- `5→5`: `3`
### Provenance
- `lean`: `3`
- `lean+manual`: `13`
- `manual`: `7`

## Observed Direct Transition Bands
| Source interval | Dependency interval | Status | File edges | Decl edges |
| --- | --- | --- | ---: | ---: |
| `0→1` | `1→1` | `healthy` | 4 | 97 |
| `1→1` | `1→1` | `healthy` | 4 | 96 |
| `3→4` | `3→4` | `healthy` | 4 | 14 |
| `3→3` | `3→3` | `healthy` | 3 | 57 |
| `3→4` | `2→3` | `healthy` | 3 | 50 |
| `3→4` | `2→4` | `healthy` | 3 | 20 |
| `3→4` | `2→2` | `healthy` | 3 | 18 |
| `1→2` | `1→1` | `healthy` | 2 | 73 |
| `2→3` | `2→2` | `healthy` | 2 | 71 |
| `2→3` | `3→3` | `healthy` | 2 | 31 |
| `5→5` | `4→5` | `healthy` | 2 | 21 |
| `4→5` | `3→3` | `healthy` | 2 | 10 |
| `5→5` | `5→5` | `healthy` | 2 | 8 |
| `1→2` | `0→1` | `healthy` | 1 | 144 |
| `2→3` | `0→1` | `healthy` | 1 | 97 |
| `3→3` | `2→2` | `healthy` | 1 | 39 |
| `2→4` | `2→3` | `healthy` | 1 | 25 |
| `2→3` | `2→3` | `healthy` | 1 | 22 |
| `4→5` | `5→5` | `healthy` | 1 | 13 |
| `2→3` | `1→2` | `healthy` | 1 | 8 |
| `1→2` | `2→2` | `healthy` | 1 | 5 |
| `2→4` | `3→4` | `healthy` | 1 | 4 |
| `2→4` | `2→2` | `healthy` | 1 | 2 |

## Top Offenders
- none

## Wormholes
- none

## Regressions
- none

## Notes
- Lean-exported tagged depths are the primary interval source where available
- the manual index remains the source of file role (`owner`, `translator`, `coherence`) and review notes
- untagged files may still be tracked through the manual index until their owner families are migrated
- capstone files should be modeled as consumers/composites, not primitive translators
