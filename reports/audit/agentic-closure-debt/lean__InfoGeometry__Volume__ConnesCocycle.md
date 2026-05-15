# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:50.858427+00:00`
Root: `lean/InfoGeometry/Volume/ConnesCocycle.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **28**
- Hard: **0**
- Soft: **25**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Volume/ConnesCocycle.lean` | `advisory` | 53 | 0 | 25 | 3 | 28 |

## Findings by file

### `lean/InfoGeometry/Volume/ConnesCocycle.lean`
- module: `InfoGeometry.Volume.ConnesCocycle`
- status: `advisory`
- debt_score: `53`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [soft] `law-field-locker` in `structure-field AdditiveModularFlow.toFun` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L36 [soft] `law-field-locker` in `structure-field AdditiveModularFlow.map_zero'` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L37 [soft] `law-field-locker` in `structure-field AdditiveModularFlow.map_add'` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L38 [soft] `law-field-locker` in `structure-field AdditiveModularFlow.instance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L42 [soft] `simp-law-injection` in `simp-declaration AdditiveModularFlow.map_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L46 [soft] `simp-law-injection` in `simp-declaration AdditiveModularFlow.map_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L132 [soft] `simp-law-injection` in `simp-declaration modularShiftAlgEquiv_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L166 [soft] `simp-law-injection` in `simp-declaration additiveModularFlowOfGenerator_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L194 [soft] `simp-law-injection` in `simp-declaration flowUnitCocycle_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L198 [soft] `skeletal-proof` in `theorem flowUnitCocycle_isConnesCocycle` — proof appears to close via minimal tactic one-liner
  - L209 [soft] `simp-law-injection` in `simp-declaration flowUnitCocycle_eq_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L215 [soft] `simp-law-injection` in `simp-declaration flowUnitCocycle_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L221 [soft] `simp-law-injection` in `simp-declaration flowUnitCocycle_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L245 [soft] `simp-law-injection` in `simp-declaration unitCocycle_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L248 [soft] `skeletal-proof` in `theorem unitCocycle_isConnesCocycle` — proof appears to close via minimal tactic one-liner
  - L258 [soft] `simp-law-injection` in `simp-declaration unitCocycle_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L263 [soft] `simp-law-injection` in `simp-declaration unitCocycle_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L286 [soft] `law-field-locker` in `structure-field ScalarCocycleBridge.toScalar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L287 [soft] `law-field-locker` in `structure-field ScalarCocycleBridge.sigma_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L337 [soft] `skeletal-proof` in `theorem scalarCocycle_zero_eq_one` — proof appears to close via minimal tactic one-liner
  - L358 [advisory] `local-hypothesis-injection` in `theorem scalarCocycle_zero_eq_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L417 [soft] `simp-law-injection` in `simp-declaration scalarCocycleDefectiveLogGenerator_eq_cocycleLogPotential` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L427 [soft] `simp-law-injection` in `simp-declaration scalarCocycle_additiveDefect_eq_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L473 [advisory] `existential-packaging` in `theorem cocycle_additive_potential` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L529 [soft] `simp-law-injection` in `simp-declaration scalarProjectiveRotorCocycle_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L539 [soft] `simp-law-injection` in `simp-declaration scalarStabilizerCharacter_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L570 [soft] `skeletal-proof` in `theorem scalarStabilizerAnomalyAtUnit_hom` — proof appears to close via minimal tactic one-liner

