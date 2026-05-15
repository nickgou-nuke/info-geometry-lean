# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:35.509928+00:00`
Root: `lean/InfoGeometry/Automorphic/LanglandsPrimeResonance.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **14**
- Hard: **0**
- Soft: **7**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Automorphic/LanglandsPrimeResonance.lean` | `advisory` | 21 | 0 | 7 | 7 | 14 |

## Findings by file

### `lean/InfoGeometry/Automorphic/LanglandsPrimeResonance.lean`
- module: `InfoGeometry.Automorphic.LanglandsPrimeResonance`
- status: `advisory`
- debt_score: `21`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L61 [soft] `law-field-locker` in `structure-field CompletedLReadout.spectralOfBoundary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L64 [soft] `law-field-locker` in `structure-field CompletedLReadout.completedL` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `law-field-locker` in `structure-field CompletedLReadout.functional_equation_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L83 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L110 [soft] `law-field-locker` in `structure-field SugawaraCentralReadout.stressOfBoundary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L113 [soft] `law-field-locker` in `structure-field SugawaraCentralReadout.centralReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L117 [soft] `law-field-locker` in `structure-field SugawaraCentralReadout.sugawara_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L132 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L165 [soft] `law-field-locker` in `structure-field LanglandsSugawaraBridge.central_eq_completedL_on_boundary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L284 [advisory] `local-hypothesis-injection` in `theorem bulk_prime_resonance_boundaryProjector_iff` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L303 [advisory] `local-hypothesis-injection` in `theorem bulk_central_zero_boundaryProjector_iff` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L407 [advisory] `existential-packaging` in `theorem langlandsPrimeResonanceWitness_nonempty_of_admissible` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L429 [advisory] `existential-packaging` in `def LanglandsPrimeResonanceOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

