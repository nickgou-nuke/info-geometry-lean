# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:01.649356+00:00`
Root: `lean/InfoGeometry/Canonical/StandardFormCore.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **31**
- Hard: **0**
- Soft: **25**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/StandardFormCore.lean` | `advisory` | 56 | 0 | 25 | 6 | 31 |

## Findings by file

### `lean/InfoGeometry/Canonical/StandardFormCore.lean`
- module: `InfoGeometry.Canonical.StandardFormCore`
- status: `advisory`
- debt_score: `56`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L37 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L60 [soft] `law-field-locker` in `structure-field StandardFormSeed.modularFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L61 [soft] `law-field-locker` in `structure-field StandardFormSeed.J_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [soft] `law-field-locker` in `structure-field StandardFormSeed.eps_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [soft] `law-field-locker` in `structure-field StandardFormSeed.phase_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `law-field-locker` in `structure-field StandardFormSeed.J_phase_anticommute` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L88 [soft] `simp-law-injection` in `simp-declaration tomitaAtomSeed_modularFlow_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L91 [soft] `simp-law-injection` in `simp-declaration tomitaAtomSeed_phaseAxis_eq_dilationOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L96 [soft] `simp-law-injection` in `simp-declaration tomitaAtomSeed_J_eq_modular_j` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L99 [soft] `simp-law-injection` in `simp-declaration tomitaAtomSeed_eps_eq_spectral_epsilon` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L102 [soft] `simp-law-injection` in `simp-declaration tomitaAtomSeed_phaseAxis_eq_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L107 [soft] `simp-law-injection` in `simp-declaration tomitaAtomSeed_phaseAxis_eq_J_comp_eps` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L112 [soft] `simp-law-injection` in `simp-declaration tomitaAtomSeed_J_comp_phaseAxis_eq_eps` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L119 [soft] `simp-law-injection` in `simp-declaration tomitaAtomSeed_phaseAxis_comp_J_eq_neg_eps` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L126 [soft] `simp-law-injection` in `simp-declaration tomitaAtomSeed_phaseAxis_comp_eps_eq_J` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L133 [soft] `simp-law-injection` in `simp-declaration tomitaAtomSeed_eps_comp_phaseAxis_eq_neg_J` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L140 [soft] `simp-law-injection` in `simp-declaration tomitaAtomSeed_eps_comp_J_eq_neg_phaseAxis` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L147 [soft] `simp-law-injection` in `simp-declaration tomitaAtomSeed_plusProjector_eq_spectralPlusProj` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L150 [soft] `simp-law-injection` in `simp-declaration tomitaAtomSeed_minusProjector_eq_spectralMinusProj` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L178 [advisory] `existential-packaging` in `structure StandardFormCarrier` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L191 [soft] `law-field-locker` in `structure-field StandardFormCarrier.modularFlow_eq_generator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L193 [soft] `simp-law-injection` in `simp-declaration StandardFormCarrier.modularFlow_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L208 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L210 [advisory] `existential-packaging` in `structure RelativeModularBridge` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L223 [soft] `law-field-locker` in `structure-field RelativeModularBridge.cocycle` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L224 [soft] `law-field-locker` in `structure-field RelativeModularBridge.scalarBridge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L244 [soft] `skeletal-proof` in `theorem RelativeModularBridge.operatorLogPotential_add` — proof appears to close via minimal tactic one-liner
  - L253 [soft] `simp-law-injection` in `simp-declaration RelativeModularBridge.projectiveModularPotential_eq_neg_projectiveLogDensity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L260 [soft] `simp-law-injection` in `simp-declaration RelativeModularBridge.projectiveModularPotential_eq_logDensity_target_sub_source` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

