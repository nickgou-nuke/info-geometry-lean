# Topic Dossier: <TOPIC>

## Executive Summary
- Status: `<GREEN|AMBER|RED>`
- Core finding: `<one-line>`
- Build surface: `<lake targets checked>`

## Lexical Surface
- Keywords: `<k1, k2, ...>`
- Namespace prefixes: `<N1, N2, ...>`
- Scan scope: `<paths>`
- Recall evidence: `<rg --stats summary>`

## Semantic Inventory
| Kind | Declaration | File | Brief |
|---|---|---|---|
| theorem | `<Namespace.thm>` | `<path>` | `<what it states>` |

## Proof/Axiom Audit
| Declaration | `#print axioms` summary | Depends on `sorryAx`? | Notes |
|---|---|---|---|
| `<Namespace.thm>` | `<axioms list>` | `<yes/no>` | `<implication>` |

## Dependency / Architecture Map
- Topic home modules: `<list>`
- Upstream critical imports: `<list>`
- Graph artifacts: `<dot/svg/json refs>`

## Maturity Block
- Green: no `sorryAx` in core theorems
- Amber: core API exists but some `sorryAx` dependence
- Red: mostly names/interfaces, weak theorem closure

Current rating for `<TOPIC>`: `<GREEN|AMBER|RED>`
Reason: `<mechanically checkable reason>`

## Socratic Layer
- Minimal definition set:
- Canonical theorems:
- Normal forms/equivalences:
- Failure modes:
- Shortest nontrivial example path:

## Open Gaps and Next Owner Surfaces
1. `<gap>` -> `<owner file + target theorem>`
2. `<gap>` -> `<owner file + target theorem>`

## Traceability
Every claim in this dossier must map to one of:
- declaration reference
- `#print axioms` output
- dependency artifact
