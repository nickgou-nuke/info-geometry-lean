# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:57.877586+00:00`
Root: `lean/InfoGeometry/LLM/SpinPinTransformerLayer.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **12**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/LLM/SpinPinTransformerLayer.lean` | `advisory` | 30 | 0 | 12 | 6 | 18 |

## Findings by file

### `lean/InfoGeometry/LLM/SpinPinTransformerLayer.lean`
- module: `InfoGeometry.LLM.SpinPinTransformerLayer`
- status: `advisory`
- debt_score: `30`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L19 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L21 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L31 [soft] `law-field-locker` in `structure-field SpinPinTransformerLayer.pin` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L38 [soft] `simp-law-injection` in `simp-declaration transport_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L44 [soft] `simp-law-injection` in `simp-declaration transport_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L50 [soft] `simp-law-injection` in `simp-declaration transport_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L63 [soft] `skeletal-proof` in `theorem run_transport_expansion` — proof appears to close via minimal tactic one-liner
  - L73 [soft] `law-field-locker` in `structure-field IsSpinEquivariant.preAttentionNorm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [soft] `law-field-locker` in `structure-field IsSpinEquivariant.attention` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L75 [soft] `law-field-locker` in `structure-field IsSpinEquivariant.preFFNNorm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L76 [soft] `law-field-locker` in `structure-field IsSpinEquivariant.feedForward` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L93 [soft] `skeletal-proof` in `theorem afterFeedForward_transport_commute` — proof appears to close via minimal tactic one-liner
  - L100 [advisory] `local-hypothesis-injection` in `theorem afterFeedForward_transport_commute` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L130 [soft] `skeletal-proof` in `theorem gap_transport_commute` — proof appears to close via minimal tactic one-liner
  - L138 [advisory] `local-hypothesis-injection` in `theorem gap_transport_commute` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L188 [advisory] `bridge-shaped-declaration` in `theorem pin44_headFactor_witness` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L188 [soft] `skeletal-proof` in `theorem pin44_headFactor_witness` — proof appears to close via minimal tactic one-liner

