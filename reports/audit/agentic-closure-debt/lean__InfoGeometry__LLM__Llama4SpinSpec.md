# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:56.707984+00:00`
Root: `lean/InfoGeometry/LLM/Llama4SpinSpec.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **8**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/LLM/Llama4SpinSpec.lean` | `advisory` | 21 | 0 | 8 | 5 | 13 |

## Findings by file

### `lean/InfoGeometry/LLM/Llama4SpinSpec.lean`
- module: `InfoGeometry.LLM.Llama4SpinSpec`
- status: `advisory`
- debt_score: `21`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L17 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L19 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L32 [soft] `law-field-locker` in `structure-field Llama4BlockSpec.residual` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L33 [soft] `law-field-locker` in `structure-field Llama4BlockSpec.moe` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L34 [soft] `law-field-locker` in `structure-field Llama4BlockSpec.spinPin` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L71 [soft] `simp-law-injection` in `simp-declaration routedUpdate_split` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L84 [soft] `law-field-locker` in `structure-field IsSplitTransportEquivariant.shared` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L86 [soft] `law-field-locker` in `structure-field IsSplitTransportEquivariant.active` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L89 [soft] `law-field-locker` in `structure-field IsSplitTransportEquivariant.defect` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L97 [soft] `skeletal-proof` in `theorem routedUpdate_transport_commute_of_split` — proof appears to close via minimal tactic one-liner
  - L107 [advisory] `local-hypothesis-injection` in `theorem routedUpdate_transport_commute_of_split` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L135 [advisory] `local-hypothesis-injection` in `theorem transport_preserves_routed_split` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

