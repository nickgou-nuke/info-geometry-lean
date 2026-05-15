# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:02.569239+00:00`
Root: `lean/InfoGeometry/Canonical/DrazinFierzBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **50**
- Hard: **0**
- Soft: **43**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DrazinFierzBridge.lean` | `advisory` | 93 | 0 | 43 | 7 | 50 |

## Findings by file

### `lean/InfoGeometry/Canonical/DrazinFierzBridge.lean`
- module: `InfoGeometry.Canonical.DrazinFierzBridge`
- status: `advisory`
- debt_score: `93`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L53 [soft] `law-field-locker` in `structure-field ExpectationState.expect` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L54 [soft] `law-field-locker` in `structure-field ExpectationState.map_add` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L57 [soft] `law-field-locker` in `structure-field ExpectationState.map_smul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [soft] `law-field-locker` in `structure-field ExpectationState.unital` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [soft] `law-field-locker` in `structure-field ExpectationState.positive_re` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `law-field-locker` in `structure-field ExpectationState.positive_im` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L83 [soft] `law-field-locker` in `structure-field BSExpectationPhi.fiber` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L86 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L102 [advisory] `existential-packaging` in `def IsInvertibleFiber` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L114 [advisory] `existential-packaging` in `def IsStableRankOneFiber` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L152 [advisory] `existential-packaging` in `def EssSeparatedFromZeroOn` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L169 [advisory] `existential-packaging` in `structure NoTraceDrazinData` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L173 [soft] `law-field-locker` in `structure-field NoTraceDrazinData.drazinFiber` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L174 [soft] `law-field-locker` in `structure-field NoTraceDrazinData.lambdaRankOne` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L175 [soft] `law-field-locker` in `structure-field NoTraceDrazinData.rankOneLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L184 [soft] `law-field-locker` in `structure-field NoTraceDrazinData.zeroLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L188 [soft] `law-field-locker` in `structure-field NoTraceDrazinData.nilpotentLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L192 [soft] `law-field-locker` in `structure-field NoTraceDrazinData.stableRankOneLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L197 [soft] `law-field-locker` in `structure-field NoTraceDrazinData.invertibleLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L216 [soft] `law-field-locker` in `structure-field DrazinFierzReadout.readout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L224 [advisory] `existential-packaging` in `theorem drazin_stable_fierz_readout` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L258 [soft] `law-field-locker` in `structure-field ExpectationFierzReadout.state` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L290 [soft] `law-field-locker` in `structure-field FierzChannelMap.channel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L330 [soft] `law-field-locker` in `structure-field NormalizedFierzCoordinates.coord` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L335 [soft] `law-field-locker` in `structure-field FierzResidual.residual` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L355 [soft] `law-field-locker` in `structure-field ExpectationOnlyFierzSocket.drazin` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L359 [soft] `law-field-locker` in `structure-field ExpectationOnlyFierzSocket.coords` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L361 [soft] `law-field-locker` in `structure-field ExpectationOnlyFierzSocket.coords_eq_expectation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L369 [soft] `law-field-locker` in `structure-field ExpectationOnlyFierzSocket.drazin_sound` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L382 [soft] `law-field-locker` in `structure-field DrazinFierzCompatibilityAssumption.residual` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L383 [soft] `law-field-locker` in `structure-field DrazinFierzCompatibilityAssumption.readout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L385 [soft] `law-field-locker` in `structure-field DrazinFierzCompatibilityAssumption.sound` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L427 [soft] `law-field-locker` in `structure-field AlternatingProjectionStrongLimitAssumption.step` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L428 [soft] `law-field-locker` in `structure-field AlternatingProjectionStrongLimitAssumption.limit` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L447 [soft] `law-field-locker` in `structure-field CenteredChannel.value` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L448 [soft] `law-field-locker` in `structure-field CenteredChannel.meanZero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L449 [soft] `law-field-locker` in `structure-field CenteredChannel.normalizedVariance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L460 [soft] `law-field-locker` in `structure-field CorrelationEnergy4.nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L485 [soft] `law-field-locker` in `structure-field Bistochastic4.nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L486 [soft] `law-field-locker` in `structure-field Bistochastic4.row_sum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L488 [soft] `law-field-locker` in `structure-field Bistochastic4.col_sum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L501 [soft] `law-field-locker` in `structure-field BirkhoffDecomposition4.weights` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L502 [soft] `law-field-locker` in `structure-field BirkhoffDecomposition4.nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L503 [soft] `law-field-locker` in `structure-field BirkhoffDecomposition4.total_weight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L505 [soft] `law-field-locker` in `structure-field BirkhoffDecomposition4.reconstruct` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L526 [soft] `law-field-locker` in `structure-field ExpectationBirkhoffSocket.rawEnergy_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L539 [soft] `law-field-locker` in `structure-field HurwitzToPermutationSocket.mul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L540 [soft] `law-field-locker` in `structure-field HurwitzToPermutationSocket.toPerm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L541 [soft] `law-field-locker` in `structure-field HurwitzToPermutationSocket.respects_mul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

