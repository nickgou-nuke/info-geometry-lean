# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:07.829890+00:00`
Root: `lean/InfoGeometry/Canonical/TypeIIILambdaCore.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **25**
- Hard: **0**
- Soft: **17**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/TypeIIILambdaCore.lean` | `advisory` | 42 | 0 | 17 | 8 | 25 |

## Findings by file

### `lean/InfoGeometry/Canonical/TypeIIILambdaCore.lean`
- module: `InfoGeometry.Canonical.TypeIIILambdaCore`
- status: `advisory`
- debt_score: `42`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L26 [soft] `law-field-locker` in `structure-field TypeIIIScaleGroup.add_closed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L27 [soft] `law-field-locker` in `structure-field TypeIIIScaleGroup.neg_closed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L33 [advisory] `existential-packaging` in `def integerPeriodSet` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L49 [soft] `simp-law-injection` in `simp-declaration integerPeriod_mem_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L51 [advisory] `existential-packaging` in `theorem integerPeriod_mem_iff` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L64 [soft] `law-field-locker` in `structure-field DiscreteTypeIIILambdaScale.hq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L102 [soft] `law-field-locker` in `structure-field ModularLambdaLattice.q_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L103 [soft] `law-field-locker` in `structure-field ModularLambdaLattice.spectralReadoutInScale` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L113 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L120 [advisory] `local-hypothesis-injection` in `theorem thermalTimeStep_mem_scale` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L143 [soft] `law-field-locker` in `structure-field MellinShift.shiftOperator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L144 [soft] `law-field-locker` in `structure-field MellinShift.shiftInverse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L145 [soft] `law-field-locker` in `structure-field MellinShift.shift_left_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L146 [soft] `law-field-locker` in `structure-field MellinShift.shift_right_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L147 [soft] `law-field-locker` in `structure-field MellinShift.weyl_covariance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L158 [soft] `law-field-locker` in `structure-field MellinSupercharge.Q` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L159 [soft] `law-field-locker` in `structure-field MellinSupercharge.nilpotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L161 [soft] `law-field-locker` in `structure-field MellinSupercharge.modular_weight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L173 [soft] `law-field-locker` in `structure-field SuperMellinAlgebra.centralOperator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L183 [soft] `law-field-locker` in `structure-field SuperMellinAlgebra.superHamiltonian_split` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L186 [soft] `law-field-locker` in `structure-field SuperMellinAlgebra.shift_supercharge_commutator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L195 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L196 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L198 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface

