# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:11.520447+00:00`
Root: `lean/InfoGeometry/Canonical/GrandCanonicalFockNumberBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **8**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/GrandCanonicalFockNumberBridge.lean` | `advisory` | 17 | 0 | 8 | 1 | 9 |

## Findings by file

### `lean/InfoGeometry/Canonical/GrandCanonicalFockNumberBridge.lean`
- module: `InfoGeometry.Canonical.GrandCanonicalFockNumberBridge`
- status: `advisory`
- debt_score: `17`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L30 [soft] `simp-law-injection` in `simp-declaration fockNumberGauge_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L33 [soft] `skeletal-proof` in `theorem fockNumberGauge_apply` — proof appears to close via minimal tactic one-liner
  - L64 [soft] `skeletal-proof` in `theorem grandCanonicalFockGenerator_eq_hamiltonian_sub_fockNumberGauge` — proof appears to close via minimal tactic one-liner
  - L75 [soft] `skeletal-proof` in `theorem fockNumberGauge_is_mu_times_numberOperator` — proof appears to close via minimal tactic one-liner
  - L102 [soft] `law-field-locker` in `structure-field FiniteFockChemicalPotentialAffineBridge.finiteGauge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L105 [soft] `law-field-locker` in `structure-field FiniteFockChemicalPotentialAffineBridge.finiteShiftedEnergy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L109 [soft] `law-field-locker` in `structure-field FiniteFockChemicalPotentialAffineBridge.fockGauge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L112 [soft] `law-field-locker` in `structure-field FiniteFockChemicalPotentialAffineBridge.fockShiftedHamiltonian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

