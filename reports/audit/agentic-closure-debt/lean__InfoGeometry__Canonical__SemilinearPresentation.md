# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:54.948085+00:00`
Root: `lean/InfoGeometry/Canonical/SemilinearPresentation.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **21**
- Hard: **0**
- Soft: **19**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SemilinearPresentation.lean` | `advisory` | 40 | 0 | 19 | 2 | 21 |

## Findings by file

### `lean/InfoGeometry/Canonical/SemilinearPresentation.lean`
- module: `InfoGeometry.Canonical.SemilinearPresentation`
- status: `advisory`
- debt_score: `40`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L29 [soft] `law-field-locker` in `structure-field ModulePresentation.act` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L31 [soft] `law-field-locker` in `structure-field ModulePresentation.support` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L32 [soft] `law-field-locker` in `structure-field ModulePresentation.generator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L33 [soft] `law-field-locker` in `structure-field ModulePresentation.metricReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L34 [soft] `law-field-locker` in `structure-field ModulePresentation.phaseReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [soft] `law-field-locker` in `structure-field SemilinearPresentationMap.mapState` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [soft] `law-field-locker` in `structure-field SemilinearPresentationMap.mapObservable` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L53 [soft] `law-field-locker` in `structure-field SemilinearPresentationMap.mapReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L54 [soft] `law-field-locker` in `structure-field SemilinearPresentationMap.map_act` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L58 [soft] `law-field-locker` in `structure-field SemilinearPresentationMap.map_support` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L61 [soft] `law-field-locker` in `structure-field SemilinearPresentationMap.map_generator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `law-field-locker` in `structure-field SemilinearPresentationMap.map_metricReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L69 [soft] `law-field-locker` in `structure-field SemilinearPresentationMap.map_phaseReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L162 [soft] `law-field-locker` in `structure-field SemilinearPresentationIso.left_state` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L165 [soft] `law-field-locker` in `structure-field SemilinearPresentationIso.right_state` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L167 [soft] `law-field-locker` in `structure-field SemilinearPresentationIso.left_observable` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L170 [soft] `law-field-locker` in `structure-field SemilinearPresentationIso.right_observable` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L172 [soft] `law-field-locker` in `structure-field SemilinearPresentationIso.left_readout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L175 [soft] `law-field-locker` in `structure-field SemilinearPresentationIso.right_readout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L328 [advisory] `local-hypothesis-injection` in `theorem pairedSwapMap_moves_state` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

