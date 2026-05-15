# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:35.797984+00:00`
Root: `lean/InfoGeometry/Automorphic/ProjectedLFunction.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **23**
- Hard: **0**
- Soft: **12**
- Advisory: **11**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Automorphic/ProjectedLFunction.lean` | `advisory` | 35 | 0 | 12 | 11 | 23 |

## Findings by file

### `lean/InfoGeometry/Automorphic/ProjectedLFunction.lean`
- module: `InfoGeometry.Automorphic.ProjectedLFunction`
- status: `advisory`
- debt_score: `35`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L43 [soft] `law-field-locker` in `structure-field AutomorphicLFunctional.coeff` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L86 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L87 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L101 [soft] `skeletal-proof` in `theorem cuspidalProjector_add_eisenstein` — proof appears to close via minimal tactic one-liner
  - L192 [advisory] `local-hypothesis-injection` in `theorem rawLFunction_eq_cuspidalLFunction_of_killsBoundary` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L217 [soft] `simp-law-injection` in `simp-declaration mem_automorphicResonanceSet_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L219 [soft] `skeletal-proof` in `theorem mem_automorphicResonanceSet_iff` — proof appears to close via minimal tactic one-liner
  - L238 [soft] `law-field-locker` in `structure-field ProjectedAutomorphicLFunctionWitness.L` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L239 [soft] `law-field-locker` in `structure-field ProjectedAutomorphicLFunctionWitness.L_eq_projected` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L273 [advisory] `existential-packaging` in `def HasEulerProduct` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L300 [soft] `law-field-locker` in `structure-field EulerProductData.localFactor` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L304 [advisory] `existential-packaging` in `def HasCompletedFunctionalEquation` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L328 [soft] `law-field-locker` in `structure-field LanglandsPrimeResonanceWitness.completedL` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L345 [soft] `law-field-locker` in `structure-field EulerProductWitness.localFactor` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L359 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L388 [soft] `law-field-locker` in `structure-field CompletedLFunctionWitness.completedL` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L398 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L443 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L492 [soft] `law-field-locker` in `structure-field LanglandsSugawaraBridge.Sugawara_L_calibration` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L519 [advisory] `existential-packaging` in `def ProjectedAutomorphicLFunctionOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L535 [soft] `skeletal-proof` in `theorem projectedAutomorphicLFunctionOwnerTarget` — proof appears to close via minimal tactic one-liner
  - L548 [advisory] `existential-packaging` in `def LanglandsPrimeResonanceOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

