# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:53.549040+00:00`
Root: `lean/InfoGeometry/Canonical/RindlerWedgeCartanBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **17**
- Hard: **0**
- Soft: **10**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RindlerWedgeCartanBridge.lean` | `advisory` | 27 | 0 | 10 | 7 | 17 |

## Findings by file

### `lean/InfoGeometry/Canonical/RindlerWedgeCartanBridge.lean`
- module: `InfoGeometry.Canonical.RindlerWedgeCartanBridge`
- status: `advisory`
- debt_score: `27`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L36 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L38 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L58 [soft] `law-field-locker` in `structure-field SelfDualRindlerWedge.standardForm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L59 [soft] `law-field-locker` in `structure-field SelfDualRindlerWedge.calibration` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L67 [soft] `skeletal-proof` in `theorem left_wedge_mem_iff_right_wedge` — proof appears to close via minimal tactic one-liner
  - L73 [soft] `skeletal-proof` in `theorem right_wedge_mem_iff_left_wedge` — proof appears to close via minimal tactic one-liner
  - L79 [soft] `skeletal-proof` in `theorem swapLeftRight_involutive` — proof appears to close via minimal tactic one-liner
  - L85 [soft] `skeletal-proof` in `theorem modular_flow_at_wedgeParameter` — proof appears to close via minimal tactic one-liner
  - L108 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L110 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L110 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L115 [soft] `skeletal-proof` in `theorem chiral_mul_mem_spectralCompact` — proof appears to close via minimal tactic one-liner
  - L125 [soft] `skeletal-proof` in `theorem chiral_commutator_mem_spectralCompact` — proof appears to close via minimal tactic one-liner
  - L136 [soft] `skeletal-proof` in `theorem compact_commutator_with_chiral_mem_chiral` — proof appears to close via minimal tactic one-liner
  - L150 [advisory] `bridge-shaped-declaration` in `theorem cartan_split_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

