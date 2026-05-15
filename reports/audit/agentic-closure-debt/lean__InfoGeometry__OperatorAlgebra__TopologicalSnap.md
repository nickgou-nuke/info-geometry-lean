# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:25.380159+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/TopologicalSnap.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **4**
- Advisory: **11**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/TopologicalSnap.lean` | `advisory` | 19 | 0 | 4 | 11 | 15 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/TopologicalSnap.lean`
- module: `InfoGeometry.OperatorAlgebra.TopologicalSnap`
- status: `advisory`
- debt_score: `19`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L30 [soft] `law-field-locker` in `structure-field ConservedObstructionFlow.invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L35 [soft] `law-field-locker` in `structure-field ConservedObstructionFlow.flow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L38 [soft] `law-field-locker` in `structure-field ConservedObstructionFlow.flat_invariant_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L42 [soft] `law-field-locker` in `structure-field ConservedObstructionFlow.flow_preserves_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L50 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L107 [advisory] `local-hypothesis-injection` in `theorem flow_preserves_nontrivial` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L126 [advisory] `local-hypothesis-injection` in `theorem invariant_eq_of_flows_to_sector` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L129 [advisory] `local-hypothesis-injection` in `theorem invariant_eq_of_flows_to_sector` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L147 [advisory] `local-hypothesis-injection` in `theorem nontrivial_cannot_flow_to_trivial_sector` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L161 [advisory] `local-hypothesis-injection` in `theorem nontrivial_cannot_flow_to_flat` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L164 [advisory] `local-hypothesis-injection` in `theorem nontrivial_cannot_flow_to_flat` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L180 [advisory] `local-hypothesis-injection` in `theorem invariant_zero_of_flows_to_flat` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L183 [advisory] `local-hypothesis-injection` in `theorem invariant_zero_of_flows_to_flat` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L210 [advisory] `existential-packaging` in `theorem no_nontrivial_flattening` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

