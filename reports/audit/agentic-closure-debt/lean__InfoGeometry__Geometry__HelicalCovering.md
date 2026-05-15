# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:37.607130+00:00`
Root: `lean/InfoGeometry/Geometry/HelicalCovering.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **32**
- Hard: **0**
- Soft: **21**
- Advisory: **11**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Geometry/HelicalCovering.lean` | `advisory` | 53 | 0 | 21 | 11 | 32 |

## Findings by file

### `lean/InfoGeometry/Geometry/HelicalCovering.lean`
- module: `InfoGeometry.Geometry.HelicalCovering`
- status: `advisory`
- debt_score: `53`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L43 [soft] `law-field-locker` in `structure-field HelicalCovering.project` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L45 [soft] `law-field-locker` in `structure-field HelicalCovering.winding` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [soft] `law-field-locker` in `structure-field HelicalCovering.branch_requires_nonzero_winding` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L66 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L102 [soft] `law-field-locker` in `structure-field WindingPreservingFlow.flow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L104 [soft] `law-field-locker` in `structure-field WindingPreservingFlow.flow_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L108 [soft] `law-field-locker` in `structure-field WindingPreservingFlow.flow_add` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L112 [soft] `law-field-locker` in `structure-field WindingPreservingFlow.preserves_winding` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L121 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L202 [soft] `law-field-locker` in `structure-field DeckAction.deck` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L204 [soft] `law-field-locker` in `structure-field DeckAction.project_deck` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L208 [soft] `law-field-locker` in `structure-field DeckAction.winding_deck` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L212 [soft] `law-field-locker` in `structure-field DeckAction.deck_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L216 [soft] `law-field-locker` in `structure-field DeckAction.deck_add` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L225 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L273 [soft] `law-field-locker` in `structure-field MonodromyEvent.projection_closed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L280 [soft] `law-field-locker` in `structure-field MonodromyEvent.winding_change` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L289 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L290 [soft] `skeletal-proof` in `theorem finish_ne_start_of_charge_ne_zero` — proof appears to close via minimal tactic one-liner
  - L296 [advisory] `local-hypothesis-injection` in `theorem finish_ne_start_of_charge_ne_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L299 [advisory] `local-hypothesis-injection` in `theorem finish_ne_start_of_charge_ne_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L318 [soft] `law-field-locker` in `structure-field SheetPacket.stateOnSheet` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L320 [soft] `law-field-locker` in `structure-field SheetPacket.amplitude` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L323 [soft] `law-field-locker` in `structure-field SheetPacket.packet_conservation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L343 [soft] `law-field-locker` in `structure-field SpectralDivisorMonodromyCalibration.logPhaseReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L346 [soft] `law-field-locker` in `structure-field SpectralDivisorMonodromyCalibration.divisor_maps_to_branch` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L352 [soft] `law-field-locker` in `structure-field SpectralDivisorMonodromyCalibration.spectral_calibration_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L363 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L376 [advisory] `existential-packaging` in `def HelicalCoveringOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L383 [advisory] `existential-packaging` in `def DeckActionOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L389 [advisory] `existential-packaging` in `def SpectralDivisorMonodromyOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

