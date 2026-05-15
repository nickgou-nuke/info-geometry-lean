# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:04.882802+00:00`
Root: `lean/InfoGeometry/Canonical/TheoryShadowRepresentation.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **5**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/TheoryShadowRepresentation.lean` | `advisory` | 17 | 0 | 5 | 7 | 12 |

## Findings by file

### `lean/InfoGeometry/Canonical/TheoryShadowRepresentation.lean`
- module: `InfoGeometry.Canonical.TheoryShadowRepresentation`
- status: `advisory`
- debt_score: `17`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L59 [soft] `law-field-locker` in `structure-field TheoryShadowRepresentation.spin44_is_finiteShadow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L61 [soft] `law-field-locker` in `structure-field TheoryShadowRepresentation.exactKKT_is_ownerOwned` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [soft] `law-field-locker` in `structure-field TheoryShadowRepresentation.splitCl44TKK_is_bridgeOwned` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `law-field-locker` in `structure-field TheoryShadowRepresentation.drazinDixmier_is_debt` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field TheoryShadowRepresentation.pfaffianWittenIndex_is_debt` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L128 [advisory] `bridge-shaped-declaration` in `theorem exactKKT_dimensionAgnostic_stationarity_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L136 [advisory] `bridge-shaped-declaration` in `theorem exactKKT_owner_constructs_stationarity_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L149 [advisory] `bridge-shaped-declaration` in `theorem exactKKT_translator_shadow_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L149 [advisory] `existential-packaging` in `theorem exactKKT_translator_shadow_packet` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L168 [advisory] `bridge-shaped-declaration` in `theorem splitCl44_TKK_shadow_bridge_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L168 [advisory] `existential-packaging` in `theorem splitCl44_TKK_shadow_bridge_packet` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

