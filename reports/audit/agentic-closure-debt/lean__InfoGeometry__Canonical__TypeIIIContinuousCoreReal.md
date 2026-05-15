# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:07.688773+00:00`
Root: `lean/InfoGeometry/Canonical/TypeIIIContinuousCoreReal.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **19**
- Hard: **0**
- Soft: **13**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/TypeIIIContinuousCoreReal.lean` | `advisory` | 32 | 0 | 13 | 6 | 19 |

## Findings by file

### `lean/InfoGeometry/Canonical/TypeIIIContinuousCoreReal.lean`
- module: `InfoGeometry.Canonical.TypeIIIContinuousCoreReal`
- status: `advisory`
- debt_score: `32`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L49 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L56 [soft] `simp-law-injection` in `simp-declaration additiveFlow_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L58 [soft] `skeletal-proof` in `theorem additiveFlow_apply` — proof appears to close via minimal tactic one-liner
  - L66 [soft] `simp-law-injection` in `simp-declaration modularFlow_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L74 [soft] `skeletal-proof` in `theorem modularFlow_add` — proof appears to close via minimal tactic one-liner
  - L108 [soft] `skeletal-proof` in `theorem modularTransportFlow_eq_realTomitaFlow` — proof appears to close via minimal tactic one-liner
  - L157 [advisory] `existential-packaging` in `theorem exists_boltzmannEntropyPotential_of_cocycle` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L175 [soft] `law-field-locker` in `structure-field RealContinuousCoreInterface.toCore` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L176 [soft] `law-field-locker` in `structure-field RealContinuousCoreInterface.dualAction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L177 [soft] `law-field-locker` in `structure-field RealContinuousCoreInterface.coreTrace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L178 [soft] `law-field-locker` in `structure-field RealContinuousCoreInterface.dualAction_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L179 [soft] `law-field-locker` in `structure-field RealContinuousCoreInterface.dualAction_add` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L181 [soft] `law-field-locker` in `structure-field RealContinuousCoreInterface.trace_dualAction_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L185 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L185 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L206 [advisory] `local-hypothesis-injection` in `theorem dualAction_preserves_dualFixed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L232 [soft] `skeletal-proof` in `theorem trace_constant_on_dualFixed` — proof appears to close via minimal tactic one-liner

