# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:11.152083+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ConformalCyclicCosmology.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **21**
- Hard: **0**
- Soft: **18**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ConformalCyclicCosmology.lean` | `advisory` | 39 | 0 | 18 | 3 | 21 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ConformalCyclicCosmology.lean`
- module: `InfoGeometry.OperatorAlgebra.ConformalCyclicCosmology`
- status: `advisory`
- debt_score: `39`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L29 [advisory] `existential-packaging` in `structure AeonConformalCrossover` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L46 [soft] `law-field-locker` in `structure-field AeonConformalCrossover.oldCarrier` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L50 [soft] `law-field-locker` in `structure-field AeonConformalCrossover.newCarrier` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L54 [soft] `law-field-locker` in `structure-field AeonConformalCrossover.old_null` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L58 [soft] `law-field-locker` in `structure-field AeonConformalCrossover.new_null` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [soft] `law-field-locker` in `structure-field AeonConformalCrossover.crossoverRel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L66 [soft] `law-field-locker` in `structure-field AeonConformalCrossover.crossover_projective` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L87 [advisory] `existential-packaging` in `theorem newCarrier_sameRay_inverted_old` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L130 [soft] `law-field-locker` in `structure-field SurvivingConformalReadout.read` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L177 [soft] `law-field-locker` in `structure-field CrossoverLightlikeGrammar.grammar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L234 [soft] `law-field-locker` in `structure-field KitaevLikeBoundaryMemoryBridge.edgeMemory` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L238 [soft] `law-field-locker` in `structure-field KitaevLikeBoundaryMemoryBridge.encode` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L242 [soft] `law-field-locker` in `structure-field KitaevLikeBoundaryMemoryBridge.edge_memory_encodes_as_grammar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L285 [soft] `law-field-locker` in `structure-field GenesisReentanglementBridge.latentOfNew` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L293 [soft] `law-field-locker` in `structure-field GenesisReentanglementBridge.reentangles` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L297 [soft] `law-field-locker` in `structure-field GenesisReentanglementBridge.reentanglement_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L354 [soft] `law-field-locker` in `structure-field CrossoverMemoryRecoveryBridge.oldMemory` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L357 [soft] `law-field-locker` in `structure-field CrossoverMemoryRecoveryBridge.newResidue` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L361 [soft] `law-field-locker` in `structure-field CrossoverMemoryRecoveryBridge.decode` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L365 [soft] `law-field-locker` in `structure-field CrossoverMemoryRecoveryBridge.recovery_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

